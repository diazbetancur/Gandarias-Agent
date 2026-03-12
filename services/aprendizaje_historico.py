# services/aprendizaje_historico.py
"""
HU 1.4 - Aprendizaje histórico compatible con Gandarias v5.0
============================================================
- Mantiene entrenamiento base desde CSV / BD
- Enriquece desde gaps, quality, suggestions, validaciones y híbridos
- Compatible con esquemas viejos y nuevos de AIModels / AITrainingHistory
- No tumba el flujo si una tabla no existe o tiene columnas distintas
"""
from __future__ import annotations

import json
import pickle
from collections import Counter, defaultdict
from datetime import date, datetime
from typing import Any, Dict, Optional, Set
from uuid import uuid4

from services.ai_scheduler import ExtractorPatrones, ModeloPatrones


class AprendizajeHistoricoService:
    def __init__(self, cursor=None, debug: bool = True):
        self.cur = cursor
        self.debug = debug
        self._extractor = ExtractorPatrones(debug=debug)
        self._modelo: Optional[ModeloPatrones] = None
        self._ensure_tables()

    def _log(self, msg: str):
        if self.debug:
            print(f"[HU1.4] {msg}")

    # ═══════════════════════════════════════════════════════════════
    # Helpers de esquema
    # ═══════════════════════════════════════════════════════════════

    def _table_exists(self, schema: str, table: str) -> bool:
        if not self.cur:
            return False
        try:
            self.cur.execute(
                """
                SELECT 1
                FROM information_schema.tables
                WHERE table_schema = %s AND table_name = %s
                LIMIT 1
                """,
                (schema, table),
            )
            return self.cur.fetchone() is not None
        except Exception:
            return False

    def _table_columns(self, schema: str, table: str) -> Set[str]:
        if not self.cur:
            return set()
        try:
            self.cur.execute(
                """
                SELECT column_name
                FROM information_schema.columns
                WHERE table_schema = %s AND table_name = %s
                """,
                (schema, table),
            )
            return {r[0] for r in self.cur.fetchall()}
        except Exception:
            return set()

    def _ensure_tables(self):
        if not self.cur:
            return
        try:
            self.cur.execute("CREATE EXTENSION IF NOT EXISTS pgcrypto;")
        except Exception:
            pass
        # Intentos no fatales; el esquema real puede existir distinto
        try:
            self.cur.execute(
                '''
                CREATE TABLE IF NOT EXISTS "Management"."AIModels" (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "Name" varchar(200) NOT NULL DEFAULT 'default',
                    "Version" varchar(50) NOT NULL DEFAULT '1.0',
                    "ModelData" bytea,
                    "TrainingStats" jsonb,
                    "IsActive" boolean NOT NULL DEFAULT false,
                    "CreatedAt" timestamp without time zone DEFAULT now(),
                    "UpdatedAt" timestamp without time zone DEFAULT now()
                );
                '''
            )
        except Exception:
            pass
        try:
            self.cur.execute(
                '''
                CREATE TABLE IF NOT EXISTS "Management"."AITrainingHistory" (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "ModelId" uuid,
                    "TrainingDate" timestamp without time zone DEFAULT now(),
                    "DataStartDate" date,
                    "DataEndDate" date,
                    "RecordsProcessed" integer DEFAULT 0,
                    "WeeksProcessed" integer DEFAULT 0,
                    "PatternsTurnos" integer DEFAULT 0,
                    "PatternsEmpWs" integer DEFAULT 0,
                    "CoverageImprovement" numeric DEFAULT 0,
                    "Notes" text
                );
                '''
            )
        except Exception:
            pass

    # ═══════════════════════════════════════════════════════════════
    # Entrenamiento base
    # ═══════════════════════════════════════════════════════════════

    def entrenar_desde_csv(self, csv_path: str) -> Dict[str, Any]:
        self._log(f"Entrenando desde CSV: {csv_path}")
        self._modelo = self._extractor.extraer_de_csv(csv_path)
        return self._modelo.to_dict()

    def entrenar_desde_bd(self, fecha_inicio: Optional[date] = None, fecha_fin: Optional[date] = None) -> Dict[str, Any]:
        if not self.cur:
            self._log("Sin cursor BD")
            return {}
        self._modelo = self._extractor.extraer_de_bd(self.cur, fecha_inicio, fecha_fin)
        self._enriquecer_con_gaps(fecha_inicio, fecha_fin)
        self._enriquecer_con_quality_scores(fecha_inicio, fecha_fin)
        self._enriquecer_con_sugerencias(fecha_inicio, fecha_fin)
        self._enriquecer_con_violaciones(fecha_inicio, fecha_fin)
        self._enriquecer_con_hibridos(fecha_inicio, fecha_fin)
        return self._modelo.to_dict()

    def entrenar_combinado(self, csv_path: str, fecha_inicio: Optional[date] = None, fecha_fin: Optional[date] = None) -> Dict[str, Any]:
        modelo_csv = self._extractor.extraer_de_csv(csv_path)
        if self.cur:
            try:
                modelo_bd = self._extractor.extraer_de_bd(self.cur, fecha_inicio, fecha_fin)
                # CSV mantiene peso completo (decay=0 → sin reducción), BD se suma encima
                self._modelo = self._merge_modelos(modelo_csv, modelo_bd, decay=1.0)
            except Exception as e:
                self._log(f"BD fallback a solo CSV: {e}")
                self._modelo = modelo_csv
            self._enriquecer_con_gaps(fecha_inicio, fecha_fin)
            self._enriquecer_con_quality_scores(fecha_inicio, fecha_fin)
            self._enriquecer_con_sugerencias(fecha_inicio, fecha_fin)
            self._enriquecer_con_violaciones(fecha_inicio, fecha_fin)
            self._enriquecer_con_hibridos(fecha_inicio, fecha_fin)
        else:
            self._modelo = modelo_csv
        return self._modelo.to_dict()

    # ═══════════════════════════════════════════════════════════════
    # Enriquecimiento
    # ═══════════════════════════════════════════════════════════════

    def _enriquecer_con_gaps(self, fecha_inicio=None, fecha_fin=None):
        if not self.cur or not self._modelo or not self._table_exists("Management", "ScheduleGaps"):
            return
        try:
            q = '''
                SELECT "Date", "WorkstationId"::text, COALESCE("GapCategory", ''), COALESCE("GapExplanation", '')
                FROM "Management"."ScheduleGaps"
                WHERE 1=1
            '''
            params = []
            if fecha_inicio:
                q += ' AND "Date" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND "Date" <= %s'
                params.append(fecha_fin)
            self.cur.execute(q, params)
            rows = self.cur.fetchall()
            ws_gap_freq = Counter()
            for _dt, ws_id, cat, explanation in rows:
                if ws_id:
                    ws_gap_freq[str(ws_id)] += 1
                try:
                    payload = json.loads(explanation) if explanation else {}
                    razones = payload.get("razones", {}) if isinstance(payload, dict) else {}
                    for k, v in razones.items():
                        self._modelo.obs_global[f"gap_reason_{k}"] = self._modelo.obs_global.get(f"gap_reason_{k}", 0) + int(v)
                except Exception:
                    pass
            self._modelo.obs_global["total_gaps_aprendidos"] = len(rows)
            self._modelo.obs_global["ws_gap_freq"] = dict(ws_gap_freq)
        except Exception as e:
            self._log(f"gaps skip: {e}")

    def _enriquecer_con_quality_scores(self, fecha_inicio=None, fecha_fin=None):
        if not self.cur or not self._modelo or not self._table_exists("Management", "ScheduleQualityShiftScores"):
            return
        try:
            q = '''
                SELECT "WorkstationName", "Score"
                FROM "Management"."ScheduleQualityShiftScores"
                WHERE 1=1
            '''
            params = []
            if fecha_inicio:
                q += ' AND "Date" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND "Date" <= %s'
                params.append(fecha_fin)
            self.cur.execute(q, params)
            rows = self.cur.fetchall()
            scores = defaultdict(list)
            for ws_name, score in rows:
                if ws_name is None:
                    continue
                try:
                    scores[str(ws_name)].append(float(score or 0))
                except Exception:
                    pass
            # también por workstation id inferida desde patrones si existe nombre exacto no siempre posible
            self._modelo.obs_global["quality_ws_avg"] = {k: round(sum(v) / len(v), 2) for k, v in scores.items() if v}
            self._modelo.obs_global["quality_records_count"] = len(rows)
        except Exception as e:
            self._log(f"quality skip: {e}")

    def _enriquecer_con_sugerencias(self, fecha_inicio=None, fecha_fin=None):
        if not self.cur or not self._modelo or not self._table_exists("Management", "ScheduleSuggestions"):
            return
        try:
            q = '''
                SELECT COALESCE("Tipo", ''), COALESCE("WorkstationsAfectadas", '[]'::jsonb)
                FROM "Management"."ScheduleSuggestions"
                WHERE 1=1
            '''
            params = []
            if fecha_inicio:
                q += ' AND "WeekStart" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND "WeekEnd" <= %s'
                params.append(fecha_fin)
            self.cur.execute(q, params)
            rows = self.cur.fetchall()
            tipo_freq = Counter()
            ws_problematicas = Counter()
            for tipo, ws_json in rows:
                if tipo:
                    tipo_freq[str(tipo)] += 1
                ws_list = ws_json if isinstance(ws_json, list) else []
                for ws in ws_list:
                    ws_problematicas[str(ws)] += 1
            self._modelo.obs_global["sugerencias_tipo_freq"] = dict(tipo_freq)
            self._modelo.obs_global["ws_problematicas_sugerencias"] = dict(ws_problematicas)
            self._modelo.obs_global["sugerencias_count"] = len(rows)
        except Exception as e:
            self._log(f"sugerencias skip: {e}")

    def _enriquecer_con_violaciones(self, fecha_inicio=None, fecha_fin=None):
        if not self.cur or not self._modelo or not self._table_exists("Management", "ScheduleRuleValidations"):
            return
        try:
            q = '''
                SELECT COALESCE("Detalle", '{}'::jsonb)
                FROM "Management"."ScheduleRuleValidations"
                WHERE 1=1
            '''
            params = []
            if fecha_inicio:
                q += ' AND "WeekStart" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND "WeekEnd" <= %s'
                params.append(fecha_fin)
            self.cur.execute(q, params)
            rows = self.cur.fetchall()
            viol_type_freq = Counter()
            ws_penalty = Counter()
            for (detalle,) in rows:
                payload = detalle if isinstance(detalle, dict) else {}
                viols = payload.get("violaciones", []) if isinstance(payload, dict) else []
                for v in viols:
                    tipo = str(v.get("tipo") or v.get("violation_type") or "")
                    if tipo:
                        viol_type_freq[tipo] += 1
                    ws = str(v.get("workstation") or v.get("workstation_name") or "")
                    if ws:
                        ws_penalty[ws] += 1
            self._modelo.obs_global["violation_type_freq"] = dict(viol_type_freq)
            self._modelo.obs_global["ws_violation_penalty"] = dict(ws_penalty)
        except Exception as e:
            self._log(f"violaciones skip: {e}")

    def _enriquecer_con_hibridos(self, fecha_inicio=None, fecha_fin=None):
        if not self.cur or not self._modelo or not self._table_exists("Management", "Schedules"):
            return
        try:
            q = '''
                SELECT "Date", "UserId"::text, "WorkstationId"::text, "StartTime", "EndTime", COALESCE("Observation", '')
                FROM "Management"."Schedules"
                WHERE COALESCE("IsDeleted", false) = false
                  AND "WorkstationId" IS NOT NULL
            '''
            params = []
            if fecha_inicio:
                q += ' AND "Date" >= %s'
                params.append(fecha_inicio)
            if fecha_fin:
                q += ' AND "Date" <= %s'
                params.append(fecha_fin)
            q += ' ORDER BY "Date", "UserId", "StartTime"'
            self.cur.execute(q, params)
            rows = self.cur.fetchall()
            by_emp_slot = defaultdict(list)
            for dt, user_id, ws_id, st, et, obs in rows:
                if obs and str(obs).startswith("HYB|"):
                    key = (str(dt), str(user_id), str(st), str(et))
                    by_emp_slot[key].append(str(ws_id))
            hybrid_pair_freq = Counter()
            for _, ws_list in by_emp_slot.items():
                uniq = sorted(set(ws_list))
                if len(uniq) == 2:
                    hybrid_pair_freq["|".join(uniq)] += 1
            self._modelo.obs_global["hybrid_pair_freq"] = dict(hybrid_pair_freq)
        except Exception as e:
            self._log(f"hibridos skip: {e}")

    # ═══════════════════════════════════════════════════════════════
    # Merge / getter
    # ═══════════════════════════════════════════════════════════════

    def _merge_modelos(self, base: ModeloPatrones, nuevo: ModeloPatrones, decay: float = 0.85) -> ModeloPatrones:
        """
        Merge incremental: combina patrones del modelo base (previo) con el nuevo.
        El decay (0.85) reduce la influencia del modelo viejo en cada iteración,
        dando más peso a los datos recientes. Esto permite que la IA 'olvide'
        gradualmente patrones obsoletos.
        """
        merged = ModeloPatrones(
            version=nuevo.version or base.version,
            fecha_entrenamiento=nuevo.fecha_entrenamiento,
            registros_procesados=int(base.registros_procesados * decay) + nuevo.registros_procesados,
            semanas_procesadas=max(base.semanas_procesadas, nuevo.semanas_procesadas),
        )
        # Afinidad emp-ws: decay frecuencia vieja + sumar nueva
        merged.afinidad_emp_ws = {}
        for k, v in base.afinidad_emp_ws.items():
            decayed = type(v)(
                emp_id=v.emp_id,
                ws_id=v.ws_id,
                frecuencia=max(1, int(v.frecuencia * decay)),
                horas_promedio=v.horas_promedio,
                dias_frecuentes=v.dias_frecuentes,
                horarios=v.horarios,
                obs_frecuente=v.obs_frecuente,
            )
            merged.afinidad_emp_ws[k] = decayed
        for k, v in nuevo.afinidad_emp_ws.items():
            if k in merged.afinidad_emp_ws:
                old = merged.afinidad_emp_ws[k]
                total_f = old.frecuencia + v.frecuencia
                merged.afinidad_emp_ws[k] = type(v)(
                    emp_id=v.emp_id,
                    ws_id=v.ws_id,
                    frecuencia=total_f,
                    horas_promedio=round((old.horas_promedio * old.frecuencia + v.horas_promedio * v.frecuencia) / max(1, total_f), 2),
                    dias_frecuentes=v.dias_frecuentes or old.dias_frecuentes,
                    horarios=list(set(old.horarios + v.horarios))[:10],
                    obs_frecuente=v.obs_frecuente,
                )
            else:
                merged.afinidad_emp_ws[k] = v

        # Horarios ws: preferir nuevos, decay viejos que no se actualizan
        merged.horarios_ws = dict(base.horarios_ws)
        merged.horarios_ws.update(nuevo.horarios_ws)

        # Carga emp: preferir nuevos, mantener viejos como fallback
        merged.carga_emp = dict(base.carga_emp)
        merged.carga_emp.update(nuevo.carga_emp)

        # obs_global: merge con decay en contadores numéricos
        merged.obs_global = {}
        for k, v in base.obs_global.items():
            if isinstance(v, (int, float)):
                merged.obs_global[k] = v * decay
            elif isinstance(v, dict):
                merged.obs_global[k] = {k2: (v2 * decay if isinstance(v2, (int, float)) else v2)
                                         for k2, v2 in v.items()}
            else:
                merged.obs_global[k] = v
        for k, v in nuevo.obs_global.items():
            if isinstance(v, (int, float)):
                merged.obs_global[k] = merged.obs_global.get(k, 0) + v
            elif isinstance(v, dict):
                cur = dict(merged.obs_global.get(k, {}) or {})
                for k2, v2 in v.items():
                    try:
                        cur[k2] = cur.get(k2, 0) + v2
                    except Exception:
                        cur[k2] = v2
                merged.obs_global[k] = cur
            else:
                merged.obs_global[k] = v

        self._log(f"Merge: base({base.registros_procesados}reg) + nuevo({nuevo.registros_procesados}reg) "
                  f"→ merged({merged.registros_procesados}reg, {len(merged.afinidad_emp_ws)} afinidades) decay={decay}")
        return merged

    @property
    def modelo(self) -> Optional[ModeloPatrones]:
        return self._modelo

    def cargar_o_entrenar(self, csv_path: str = None, fecha_inicio: Optional[date] = None, fecha_fin: Optional[date] = None) -> ModeloPatrones:
        if self.cur and self._cargar_modelo_activo():
            return self._modelo
        if csv_path:
            self.entrenar_combinado(csv_path, fecha_inicio, fecha_fin)
        elif self.cur:
            self.entrenar_desde_bd(fecha_inicio, fecha_fin)
        else:
            self._modelo = ModeloPatrones()
        return self._modelo

    # ═══════════════════════════════════════════════════════════════
    # Persistencia modelo / histórico
    # ═══════════════════════════════════════════════════════════════

    def guardar_modelo(self, nombre: str = "default", version: str = "5.0") -> str:
        if not self.cur or not self._modelo or not self._table_exists("Management", "AIModels"):
            return ""
        cols = self._table_columns("Management", "AIModels")
        model_id = str(uuid4())
        stats_json = json.dumps(self._modelo.to_dict(), ensure_ascii=False)
        blob = pickle.dumps(self._modelo)
        try:
            if "IsActive" in cols:
                self.cur.execute('UPDATE "Management"."AIModels" SET "IsActive" = false WHERE "IsActive" = true')
            final_cols = []
            final_placeholders = []
            final_values = []
            ordered = [("Id", model_id), ("Name", nombre), ("Version", version), ("ModelData", blob)]
            for col, val in ordered:
                if col in cols:
                    final_cols.append(f'"{col}"')
                    final_placeholders.append('%s')
                    final_values.append(val)
            if "TrainingStats" in cols:
                final_cols.append('"TrainingStats"')
                final_placeholders.append('%s::jsonb')
                final_values.append(stats_json)
            elif "Metadata" in cols:
                final_cols.append('"Metadata"')
                final_placeholders.append('%s::jsonb')
                final_values.append(stats_json)
            if "IsActive" in cols:
                final_cols.append('"IsActive"')
                final_placeholders.append('true')
            if "CreatedAt" in cols:
                final_cols.append('"CreatedAt"')
                final_placeholders.append('now()')
            if "UpdatedAt" in cols:
                final_cols.append('"UpdatedAt"')
                final_placeholders.append('now()')
            sql = f'INSERT INTO "Management"."AIModels" ({", ".join(final_cols)}) VALUES ({", ".join(final_placeholders)})'
            self.cur.execute(sql, tuple(final_values))
            return model_id
        except Exception as e:
            self._log(f"guardar_modelo skip: {e}")
            return ""

    def _cargar_modelo_activo(self) -> bool:
        if not self.cur or not self._table_exists("Management", "AIModels"):
            return False
        cols = self._table_columns("Management", "AIModels")
        if "ModelData" not in cols:
            return False
        try:
            where_clause = 'WHERE "IsActive" = true' if 'IsActive' in cols else ''
            order_clause = 'ORDER BY "UpdatedAt" DESC, "CreatedAt" DESC' if 'UpdatedAt' in cols and 'CreatedAt' in cols else ('ORDER BY "CreatedAt" DESC' if 'CreatedAt' in cols else '')
            self.cur.execute(f'SELECT "Id", "ModelData" FROM "Management"."AIModels" {where_clause} {order_clause} LIMIT 1')
            row = self.cur.fetchone()
            if not row or not row[1]:
                return False
            data = bytes(row[1]) if isinstance(row[1], memoryview) else row[1]
            self._modelo = pickle.loads(data)
            return True
        except Exception as e:
            self._log(f"cargar_modelo skip: {e}")
            return False

    def registrar_training_history(self, model_id: str, data_start: Optional[date] = None, data_end: Optional[date] = None, notes: str = "", coverage_improvement: float = 0.0) -> None:
        if not self.cur or not self._modelo or not self._table_exists("Management", "AITrainingHistory"):
            return
        cols = self._table_columns("Management", "AITrainingHistory")
        values_by_col = {
            "Id": str(uuid4()),
            "ModelId": model_id or None,
            "TrainingDate": datetime.utcnow(),
            "DataStartDate": data_start,
            "DataEndDate": data_end,
            "RecordsProcessed": getattr(self._modelo, "registros_procesados", 0),
            "WeeksProcessed": getattr(self._modelo, "semanas_procesadas", 0),
            "PatternsTurnos": len(getattr(self._modelo, "horarios_ws", {}) or {}),
            "PatternsEmpWs": len(getattr(self._modelo, "afinidad_emp_ws", {}) or {}),
            "CoverageImprovement": coverage_improvement,
            "Notes": notes,
            # compat español viejo
            "RegistrosProcesados": getattr(self._modelo, "registros_procesados", 0),
            "SemanasProcesadas": getattr(self._modelo, "semanas_procesadas", 0),
            "PatronesHorario": len(getattr(self._modelo, "horarios_ws", {}) or {}),
            "PatronesAfinidad": len(getattr(self._modelo, "afinidad_emp_ws", {}) or {}),
            "PatronesCarga": len(getattr(self._modelo, "carga_emp", {}) or {}),
            "CreatedAt": datetime.utcnow(),
        }
        preferred = [
            "Id", "ModelId", "TrainingDate", "DataStartDate", "DataEndDate", "RecordsProcessed", "WeeksProcessed",
            "PatternsTurnos", "PatternsEmpWs", "CoverageImprovement", "Notes",
            "RegistrosProcesados", "SemanasProcesadas", "PatronesHorario", "PatronesAfinidad", "PatronesCarga", "CreatedAt",
        ]
        final_cols, final_placeholders, final_values = [], [], []
        for col in preferred:
            if col in cols:
                final_cols.append(f'"{col}"')
                final_placeholders.append('%s')
                final_values.append(values_by_col[col])
        if not final_cols:
            return
        try:
            sql = f'INSERT INTO "Management"."AITrainingHistory" ({", ".join(final_cols)}) VALUES ({", ".join(final_placeholders)})'
            self.cur.execute(sql, tuple(final_values))
        except Exception as e:
            self._log(f"training_history skip: {e}")

    def get_status(self) -> Dict[str, Any]:
        if self._modelo:
            return {"entrenado": True, "modelo": self._modelo.to_dict()}
        return {"entrenado": False}