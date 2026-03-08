# services/aprendizaje_historico.py
"""
HU 1.4 - IA que Aprende del Histórico de Turnos (v4.2 MEJORADO)
================================================================
MEJORAS v4.2:
  - Entrena también desde ScheduleGaps (HU 1.1):
    → Penaliza afinidad emp↔ws donde hay gaps frecuentes
    → Aprende qué workstations/horarios son problemáticos
  - Entrena desde ScheduleQualityShiftScores (HU 1.2):
    → Refuerza patrones con alto score
    → Reduce peso de patrones con bajo score
  - Entrena desde ScheduleSuggestions (HU 1.3):
    → Incorpora señales de sobrecarga/subutilización
  - El modelo resultante influye en el Scorer de ai_scheduler.py

VERSIÓN COMPATIBLE CON ESQUEMAS VIEJOS DE BD:
  - No exige columna "Metadata" en AIModels
  - No exige columnas avanzadas en AITrainingHistory
  - Inserta solo en las columnas que realmente existen
  - Si no puede persistir histórico/modelo, no tumba el flujo principal
"""
from __future__ import annotations

import json
import pickle
from datetime import date
from typing import Any, Dict, Optional, Set
from uuid import uuid4

from services.ai_scheduler import (
    ExtractorPatrones,
    ModeloPatrones,
)


class AprendizajeHistoricoService:
    """
    Servicio unificado de entrenamiento y persistencia del modelo IA.
    v4.2: Entrena combinando Schedules + Gaps + Quality + Suggestions.
    """

    def __init__(self, cursor=None, debug: bool = True):
        self.cur = cursor
        self.debug = debug
        self._extractor = ExtractorPatrones(debug=debug)
        self._modelo: Optional[ModeloPatrones] = None
        self._ensure_tables()

    def _log(self, msg: str):
        if self.debug:
            print(f"[HU1.4] {msg}")

    # =========================================================
    # UTILIDADES DE ESQUEMA / COMPATIBILIDAD BD
    # =========================================================

    def _table_exists(self, schema: str, table: str) -> bool:
        if not self.cur:
            return False
        try:
            self.cur.execute("""
                SELECT 1
                FROM information_schema.tables
                WHERE table_schema = %s
                  AND table_name = %s
                LIMIT 1
            """, (schema, table))
            return self.cur.fetchone() is not None
        except Exception as e:
            self._log(f"_table_exists({schema}.{table}) error: {e}")
            return False

    def _table_columns(self, schema: str, table: str) -> Set[str]:
        if not self.cur:
            return set()
        try:
            self.cur.execute("""
                SELECT column_name
                FROM information_schema.columns
                WHERE table_schema = %s
                  AND table_name = %s
            """, (schema, table))
            return {row[0] for row in self.cur.fetchall()}
        except Exception as e:
            self._log(f"_table_columns({schema}.{table}) error: {e}")
            return set()

    def _table_has_column(self, schema: str, table: str, column: str) -> bool:
        return column in self._table_columns(schema, table)

    def _ensure_tables(self):
        """
        Intenta crear tablas si no existen, pero nunca falla de forma fatal
        si el usuario no tiene permisos o si el esquema ya existe distinto.
        """
        if not self.cur:
            return

        # pgcrypto para gen_random_uuid() si existe permiso
        try:
            self.cur.execute("""CREATE EXTENSION IF NOT EXISTS pgcrypto;""")
        except Exception as e:
            self._log(f"pgcrypto no disponible/sin permisos: {e}")

        try:
            self.cur.execute("""
                CREATE TABLE IF NOT EXISTS "Management"."AIModels" (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "Name" text NOT NULL DEFAULT 'default',
                    "Version" text NOT NULL DEFAULT '1.0',
                    "ModelData" bytea,
                    "Metadata" jsonb,
                    "IsActive" boolean NOT NULL DEFAULT false,
                    "CreatedAt" timestamp without time zone DEFAULT now()
                );
            """)
        except Exception as e:
            self._log(f'AIModels create skipped/no permitido: {e}')

        try:
            self.cur.execute("""
                CREATE TABLE IF NOT EXISTS "Management"."AITrainingHistory" (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "ModelId" uuid,
                    "DataStartDate" date,
                    "DataEndDate" date,
                    "RegistrosProcesados" integer DEFAULT 0,
                    "SemanasProcesadas" integer DEFAULT 0,
                    "PatronesAfinidad" integer DEFAULT 0,
                    "PatronesHorario" integer DEFAULT 0,
                    "PatronesCarga" integer DEFAULT 0,
                    "CoverageImprovement" float DEFAULT 0.0,
                    "Notes" text,
                    "CreatedAt" timestamp without time zone DEFAULT now()
                );
            """)
        except Exception as e:
            self._log(f'AITrainingHistory create skipped/no permitido: {e}')

        try:
            self.cur.execute("""
                CREATE TABLE IF NOT EXISTS "Management"."AIPredictions" (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "ModelId" uuid,
                    "Token" text,
                    "Date" date,
                    "WorkstationId" uuid,
                    "UserId" uuid,
                    "StartTime" interval,
                    "EndTime" interval,
                    "Confidence" float DEFAULT 0.0,
                    "Applied" boolean DEFAULT false,
                    "CreatedAt" timestamp without time zone DEFAULT now()
                );
            """)
        except Exception as e:
            self._log(f'AIPredictions create skipped/no permitido: {e}')

    # =========================================================
    # ENTRENAMIENTO BASE (schedules)
    # =========================================================

    def entrenar_desde_csv(self, csv_path: str) -> Dict[str, Any]:
        self._log(f"Entrenando desde CSV: {csv_path}")
        self._modelo = self._extractor.extraer_de_csv(csv_path)
        stats = self._modelo.to_dict()
        self._log(f"Entrenamiento CSV completado: {stats}")
        return stats

    def entrenar_desde_bd(
        self,
        fecha_inicio: Optional[date] = None,
        fecha_fin: Optional[date] = None,
    ) -> Dict[str, Any]:
        if not self.cur:
            self._log("Sin cursor BD, no se puede entrenar desde BD")
            return {}

        self._log(f"Entrenando desde BD: {fecha_inicio} → {fecha_fin}")
        self._modelo = self._extractor.extraer_de_bd(self.cur, fecha_inicio, fecha_fin)

        # Enriquecimiento con feedback HU 1.1 / 1.2 / 1.3
        self._enriquecer_con_gaps(fecha_inicio, fecha_fin)
        self._enriquecer_con_quality_scores(fecha_inicio, fecha_fin)
        self._enriquecer_con_sugerencias(fecha_inicio, fecha_fin)

        stats = self._modelo.to_dict()
        self._log(f"Entrenamiento BD completado (con feedback HU 1.1/1.2/1.3): {stats}")
        return stats

    def entrenar_combinado(
        self,
        csv_path: str,
        fecha_inicio: Optional[date] = None,
        fecha_fin: Optional[date] = None,
    ) -> Dict[str, Any]:
        modelo_csv = self._extractor.extraer_de_csv(csv_path)

        if self.cur:
            try:
                modelo_bd = self._extractor.extraer_de_bd(self.cur, fecha_inicio, fecha_fin)
                self._modelo = self._merge_modelos(modelo_csv, modelo_bd)
            except Exception as e:
                self._log(f"BD fallback a solo CSV: {e}")
                self._modelo = modelo_csv
        else:
            self._modelo = modelo_csv

        if self.cur:
            self._enriquecer_con_gaps(fecha_inicio, fecha_fin)
            self._enriquecer_con_quality_scores(fecha_inicio, fecha_fin)
            self._enriquecer_con_sugerencias(fecha_inicio, fecha_fin)

        stats = self._modelo.to_dict()
        self._log(f"Entrenamiento combinado: {stats}")
        return stats

    # =========================================================
    # ENRIQUECIMIENTO CON FEEDBACK
    # =========================================================

    def _enriquecer_con_gaps(self, fecha_inicio=None, fecha_fin=None):
        """
        Lee ScheduleGaps para aprender qué ws/horarios tienen problemas.
        Reduce la afinidad de workstations problemáticas.
        """
        if not self.cur or not self._modelo:
            return

        if not self._table_exists("Management", "ScheduleGaps"):
            self._log("ScheduleGaps no existe; se omite enriquecimiento de gaps")
            return

        try:
            q = '''
                SELECT g."Date", g."WorkstationId"::text, g."GapCategory", g."GapExplanation"
                FROM "Management"."ScheduleGaps" g
                WHERE 1=1
            '''
            params = []
            if fecha_inicio:
                q += ' AND g."Date" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND g."Date" <= %s'
                params.append(fecha_fin)

            self.cur.execute(q, params)
            rows = self.cur.fetchall()

            gap_count = 0
            ws_gap_freq: Dict[str, int] = {}

            for row in rows:
                gap_count += 1
                ws_id = row[1]

                if ws_id:
                    ws_gap_freq[ws_id] = ws_gap_freq.get(ws_id, 0) + 1

                    try:
                        explanation = json.loads(row[3]) if row[3] else {}
                        razones = explanation.get("razones", {})
                        if isinstance(razones, dict):
                            for razon, count in razones.items():
                                key = f"gap_reason_{razon}"
                                self._modelo.obs_global[key] = self._modelo.obs_global.get(key, 0) + int(count)
                    except (json.JSONDecodeError, TypeError, ValueError):
                        pass

            # Penalizar workstations con muchos gaps
            for ws_id, freq in ws_gap_freq.items():
                for key, pat in self._modelo.horarios_ws.items():
                    if key[0] == ws_id and freq > 2:
                        pat.frecuencia = max(1, pat.frecuencia - freq // 2)

            self._modelo.obs_global["total_gaps_aprendidos"] = gap_count
            self._modelo.obs_global["ws_gap_freq"] = ws_gap_freq
            self._log(f"Enriquecido con {gap_count} gaps de BD")

        except Exception as e:
            self._log(f"Error enriqueciendo con gaps: {e}")

    def _enriquecer_con_quality_scores(self, fecha_inicio=None, fecha_fin=None):
        """
        Lee ScheduleQualityShiftScores para reforzar patrones de alto score
        y penalizar los de bajo score.
        """
        if not self.cur or not self._modelo:
            return

        if not self._table_exists("Management", "ScheduleQualityShiftScores"):
            self._log("ScheduleQualityShiftScores no existe; se omite enriquecimiento de quality")
            return

        try:
            q = '''
                SELECT sq."WorkstationName", sq."Score", sq."CoverageScore",
                       sq."FairnessScore", sq."RulesScore", sq."Date"
                FROM "Management"."ScheduleQualityShiftScores" sq
                WHERE 1=1
            '''
            params = []
            if fecha_inicio:
                q += ' AND sq."Date" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND sq."Date" <= %s'
                params.append(fecha_fin)

            self.cur.execute(q, params)
            rows = self.cur.fetchall()

            if not rows:
                self._log("Sin quality scores en BD para enriquecer")
                return

            ws_scores: Dict[str, list] = {}
            for row in rows:
                ws_name = row[0]
                score = float(row[1]) if row[1] is not None else 0.0
                if ws_name not in ws_scores:
                    ws_scores[ws_name] = []
                ws_scores[ws_name].append(score)

            ws_avg_scores = {
                ws: sum(scores) / len(scores)
                for ws, scores in ws_scores.items()
                if scores
            }

            self._modelo.obs_global["quality_ws_avg"] = ws_avg_scores
            self._modelo.obs_global["quality_records_count"] = len(rows)

            self._log(
                f"Enriquecido con {len(rows)} quality scores. "
                f"WS scores: {ws_avg_scores}"
            )

        except Exception as e:
            self._log(f"Error enriqueciendo con quality scores: {e}")

    def _enriquecer_con_sugerencias(self, fecha_inicio=None, fecha_fin=None):
        """
        Lee ScheduleSuggestions para incorporar señales de mejora.
        """
        if not self.cur or not self._modelo:
            return

        if not self._table_exists("Management", "ScheduleSuggestions"):
            self._log("ScheduleSuggestions no existe; se omite enriquecimiento de sugerencias")
            return

        try:
            q = '''
                SELECT ss."Tipo", ss."Prioridad", ss."WorkstationsAfectadas",
                       ss."EmpleadosInvolucrados", ss."MejoraEstimada"
                FROM "Management"."ScheduleSuggestions" ss
                WHERE 1=1
            '''
            params = []
            if fecha_inicio:
                q += ' AND ss."WeekStart" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND ss."WeekEnd" <= %s'
                params.append(fecha_fin)

            self.cur.execute(q, params)
            rows = self.cur.fetchall()

            if not rows:
                self._log("Sin sugerencias en BD para enriquecer")
                return

            tipo_freq: Dict[str, int] = {}
            ws_problematicas: Dict[str, int] = {}

            for row in rows:
                tipo = row[0]
                tipo_freq[tipo] = tipo_freq.get(tipo, 0) + 1

                try:
                    ws_list = json.loads(row[2]) if row[2] else []
                    if isinstance(ws_list, list):
                        for ws in ws_list:
                            ws_problematicas[ws] = ws_problematicas.get(ws, 0) + 1
                except (json.JSONDecodeError, TypeError):
                    pass

            self._modelo.obs_global["sugerencias_tipo_freq"] = tipo_freq
            self._modelo.obs_global["ws_problematicas_sugerencias"] = ws_problematicas
            self._modelo.obs_global["sugerencias_count"] = len(rows)

            self._log(
                f"Enriquecido con {len(rows)} sugerencias. "
                f"Tipos: {tipo_freq}"
            )

        except Exception as e:
            self._log(f"Error enriqueciendo con sugerencias: {e}")

    # =========================================================
    # MERGE DE MODELOS
    # =========================================================

    def _merge_modelos(self, base: ModeloPatrones, nuevo: ModeloPatrones) -> ModeloPatrones:
        merged = ModeloPatrones(
            version=nuevo.version,
            fecha_entrenamiento=nuevo.fecha_entrenamiento,
            registros_procesados=base.registros_procesados + nuevo.registros_procesados,
            semanas_procesadas=max(base.semanas_procesadas, nuevo.semanas_procesadas),
        )

        merged.afinidad_emp_ws = dict(base.afinidad_emp_ws)
        for k, v in nuevo.afinidad_emp_ws.items():
            if k in merged.afinidad_emp_ws:
                old = merged.afinidad_emp_ws[k]
                total_f = old.frecuencia + v.frecuencia
                merged.afinidad_emp_ws[k] = type(v)(
                    emp_id=v.emp_id,
                    ws_id=v.ws_id,
                    frecuencia=total_f,
                    horas_promedio=round(
                        (old.horas_promedio * old.frecuencia + v.horas_promedio * v.frecuencia) / max(1, total_f),
                        2
                    ),
                    dias_frecuentes=v.dias_frecuentes or old.dias_frecuentes,
                    horarios=list(set(old.horarios + v.horarios))[:10],
                    obs_frecuente=v.obs_frecuente,
                )
            else:
                merged.afinidad_emp_ws[k] = v

        merged.horarios_ws = dict(base.horarios_ws)
        merged.horarios_ws.update(nuevo.horarios_ws)

        merged.carga_emp = dict(base.carga_emp)
        merged.carga_emp.update(nuevo.carga_emp)

        merged.obs_global = dict(base.obs_global)
        for k, v in nuevo.obs_global.items():
            if isinstance(v, (int, float)):
                merged.obs_global[k] = merged.obs_global.get(k, 0) + v
            else:
                merged.obs_global[k] = v

        return merged

    # =========================================================
    # MODELO GETTER
    # =========================================================

    @property
    def modelo(self) -> Optional[ModeloPatrones]:
        return self._modelo

    def cargar_o_entrenar(
        self,
        csv_path: str = None,
        fecha_inicio: Optional[date] = None,
        fecha_fin: Optional[date] = None,
    ) -> ModeloPatrones:
        if self.cur and self._cargar_modelo_activo():
            self._log("Modelo activo cargado desde BD")
            return self._modelo

        if csv_path:
            self.entrenar_combinado(csv_path, fecha_inicio, fecha_fin)
        elif self.cur:
            self.entrenar_desde_bd(fecha_inicio, fecha_fin)
        else:
            self._log("Sin CSV ni BD: modelo vacío")
            self._modelo = ModeloPatrones()

        return self._modelo

    # =========================================================
    # PERSISTENCIA DE MODELO
    # =========================================================

    def guardar_modelo(self, nombre: str = "default", version: str = "4.2") -> str:
        """
        Guarda el modelo en AIModels de forma compatible con esquemas viejos.
        Si existe Metadata, la usa; si no, guarda sin esa columna.
        """
        if not self.cur or not self._modelo:
            return ""

        if not self._table_exists("Management", "AIModels"):
            self._log("AIModels no existe; se omite guardado del modelo")
            return ""

        cols = self._table_columns("Management", "AIModels")
        if not cols:
            self._log("No se pudieron leer columnas de AIModels; se omite guardado del modelo")
            return ""

        model_id = str(uuid4())
        model_data = pickle.dumps(self._modelo)
        metadata = json.dumps(self._modelo.to_dict(), ensure_ascii=False)

        try:
            if "IsActive" in cols:
                self.cur.execute("""
                    UPDATE "Management"."AIModels"
                    SET "IsActive" = false
                    WHERE "IsActive" = true
                """)

            # Construcción dinámica del INSERT según columnas reales
            final_cols = []
            final_placeholders = []
            final_values = []

            ordered_candidates = [
                ("Id", model_id),
                ("Name", nombre),
                ("Version", version),
                ("ModelData", model_data),
            ]

            for col, val in ordered_candidates:
                if col in cols:
                    final_cols.append(f'"{col}"')
                    final_placeholders.append("%s")
                    final_values.append(val)

            if "Metadata" in cols:
                final_cols.append('"Metadata"')
                final_placeholders.append("%s::jsonb")
                final_values.append(metadata)

            if "IsActive" in cols:
                final_cols.append('"IsActive"')
                final_placeholders.append("true")

            if "CreatedAt" in cols:
                final_cols.append('"CreatedAt"')
                final_placeholders.append("now()")

            if not final_cols:
                self._log("AIModels existe pero no tiene columnas utilizables")
                return ""

            sql = f'''
                INSERT INTO "Management"."AIModels"
                    ({", ".join(final_cols)})
                VALUES ({", ".join(final_placeholders)})
            '''

            self.cur.execute(sql, tuple(final_values))
            self._log(f"Modelo guardado: {model_id} ({nombre} v{version})")
            return model_id

        except Exception as e:
            self._log(f"Error guardando modelo: {e}")
            return ""

    def _cargar_modelo_activo(self) -> bool:
        """
        Carga el último modelo activo si la tabla/columnas existen.
        Compatible con esquemas viejos.
        """
        if not self.cur:
            return False

        if not self._table_exists("Management", "AIModels"):
            return False

        cols = self._table_columns("Management", "AIModels")
        if not cols or "ModelData" not in cols:
            self._log("AIModels no tiene ModelData; no se puede cargar modelo activo")
            return False

        try:
            where_clause = 'WHERE "IsActive" = true' if "IsActive" in cols else ""
            order_clause = 'ORDER BY "CreatedAt" DESC' if "CreatedAt" in cols else ""

            self.cur.execute(f'''
                SELECT "Id", "ModelData"
                FROM "Management"."AIModels"
                {where_clause}
                {order_clause}
                LIMIT 1
            ''')

            row = self.cur.fetchone()
            if row and row[1]:
                data = row[1]
                if isinstance(data, memoryview):
                    data = bytes(data)
                self._modelo = pickle.loads(data)
                self._log(f"Modelo activo cargado: {row[0]}")
                return True

        except Exception as e:
            self._log(f"Error cargando modelo: {e}")

        return False

    # =========================================================
    # PERSISTENCIA DE HISTÓRICO
    # =========================================================

    def registrar_training_history(
        self,
        model_id: str,
        data_start: Optional[date] = None,
        data_end: Optional[date] = None,
        notes: str = "",
        coverage_improvement: float = 0.0,
    ) -> None:
        """
        Inserta histórico solo en las columnas que existan realmente
        en AITrainingHistory. Si la tabla es vieja, se degrada elegantemente.
        """
        if not self.cur or not self._modelo:
            return

        if not self._table_exists("Management", "AITrainingHistory"):
            self._log("AITrainingHistory no existe; se omite histórico")
            return

        cols = self._table_columns("Management", "AITrainingHistory")
        if not cols:
            self._log("No se pudieron leer columnas de AITrainingHistory; se omite histórico")
            return

        values_by_col = {
            "Id": str(uuid4()),
            "ModelId": model_id if model_id else None,
            "DataStartDate": data_start,
            "DataEndDate": data_end,
            "RegistrosProcesados": getattr(self._modelo, "registros_procesados", 0),
            "SemanasProcesadas": getattr(self._modelo, "semanas_procesadas", 0),
            "PatronesAfinidad": len(getattr(self._modelo, "afinidad_emp_ws", {}) or {}),
            "PatronesHorario": len(getattr(self._modelo, "horarios_ws", {}) or {}),
            "PatronesCarga": len(getattr(self._modelo, "carga_emp", {}) or {}),
            "CoverageImprovement": coverage_improvement,
            "Notes": notes,
        }

        ordered_candidates = [
            "Id",
            "ModelId",
            "DataStartDate",
            "DataEndDate",
            "RegistrosProcesados",
            "SemanasProcesadas",
            "PatronesAfinidad",
            "PatronesHorario",
            "PatronesCarga",
            "CoverageImprovement",
            "Notes",
        ]

        final_cols = []
        final_placeholders = []
        final_values = []

        for col in ordered_candidates:
            if col in cols:
                final_cols.append(f'"{col}"')
                final_placeholders.append("%s")
                final_values.append(values_by_col[col])

        if "CreatedAt" in cols:
            final_cols.append('"CreatedAt"')
            final_placeholders.append("now()")

        if not final_cols:
            self._log("AITrainingHistory existe pero no tiene columnas utilizables")
            return

        sql = f'''
            INSERT INTO "Management"."AITrainingHistory"
                ({", ".join(final_cols)})
            VALUES ({", ".join(final_placeholders)})
        '''

        try:
            self.cur.execute(sql, tuple(final_values))
            self._log(
                "AITrainingHistory guardado con columnas: "
                + ", ".join(col.replace('"', '') for col in final_cols)
            )
        except Exception as e:
            self._log(f"Se omite AITrainingHistory por incompatibilidad de esquema: {e}")

    # =========================================================
    # STATUS
    # =========================================================

    def get_status(self) -> Dict[str, Any]:
        if self._modelo:
            return {
                "entrenado": True,
                "modelo": self._modelo.to_dict(),
            }
        return {"entrenado": False}