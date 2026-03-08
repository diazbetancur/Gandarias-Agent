# services/aprendizaje_historico.py
"""
HU 1.4 - IA que Aprende del Histórico de Turnos (REESCRITO v4.0)
=================================================================
Componente de aprendizaje continuo para el motor de IA.

ANTES: Refinaba schedules del CP-SAT (violaba reglas).
AHORA: Entrena el ModeloPatrones que usa AIScheduleGenerator directamente.
       NO toca el schedule generado — solo alimenta el modelo.

FLUJO:
  1. Extrae patrones de CSV inicial (primer entrenamiento)
  2. Cada ejecución de save() re-entrena con datos BD acumulados
  3. Persiste modelo en AIModels, historial en AITrainingHistory
  4. El modelo se usa en la próxima generación de schedule
"""
from __future__ import annotations

import json
import pickle
from datetime import datetime, date, timedelta
from typing import Any, Dict, List, Optional
from uuid import uuid4

from services.ai_scheduler import (
    ExtractorPatrones,
    ModeloPatrones,
)


# ═══════════════════════════════════════════════════════════════════
# SERVICIO PRINCIPAL
# ═══════════════════════════════════════════════════════════════════

class AprendizajeHistoricoService:
    """
    Servicio unificado de entrenamiento y persistencia del modelo IA.
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

    def _ensure_tables(self):
        """Auto-crea tablas necesarias si no existen."""
        if not self.cur:
            return
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
            self.cur.execute("""
                CREATE TABLE IF NOT EXISTS "Management"."AITrainingHistory" (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "ModelId" uuid REFERENCES "Management"."AIModels"("Id"),
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
            self.cur.execute("""
                CREATE TABLE IF NOT EXISTS "Management"."AIPredictions" (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "ModelId" uuid REFERENCES "Management"."AIModels"("Id"),
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
            self._log(f"ensure_tables (no-fatal): {e}")

    # ─────────────────────────────────────────
    # ENTRENAMIENTO
    # ─────────────────────────────────────────

    def entrenar_desde_csv(self, csv_path: str) -> Dict[str, Any]:
        """Entrena modelo desde archivo CSV."""
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
        """Entrena modelo desde datos en BD."""
        if not self.cur:
            self._log("Sin cursor BD, no se puede entrenar desde BD")
            return {}
        self._log(f"Entrenando desde BD: {fecha_inicio} → {fecha_fin}")
        self._modelo = self._extractor.extraer_de_bd(self.cur, fecha_inicio, fecha_fin)
        stats = self._modelo.to_dict()
        self._log(f"Entrenamiento BD completado: {stats}")
        return stats

    def entrenar_combinado(
        self,
        csv_path: str,
        fecha_inicio: Optional[date] = None,
        fecha_fin: Optional[date] = None,
    ) -> Dict[str, Any]:
        """
        Entrena combinando CSV + BD.
        Prioriza BD si hay datos recientes; CSV como base.
        """
        # Primero CSV como base
        modelo_csv = self._extractor.extraer_de_csv(csv_path)

        # Luego BD si hay cursor
        if self.cur:
            try:
                modelo_bd = self._extractor.extraer_de_bd(self.cur, fecha_inicio, fecha_fin)
                # Merge: BD tiene prioridad (datos más recientes)
                self._modelo = self._merge_modelos(modelo_csv, modelo_bd)
            except Exception as e:
                self._log(f"BD fallback a solo CSV: {e}")
                self._modelo = modelo_csv
        else:
            self._modelo = modelo_csv

        stats = self._modelo.to_dict()
        self._log(f"Entrenamiento combinado: {stats}")
        return stats

    def _merge_modelos(self, base: ModeloPatrones, nuevo: ModeloPatrones) -> ModeloPatrones:
        """Merge de 2 modelos: nuevo tiene prioridad."""
        merged = ModeloPatrones(
            version=nuevo.version,
            fecha_entrenamiento=nuevo.fecha_entrenamiento,
            registros_procesados=base.registros_procesados + nuevo.registros_procesados,
            semanas_procesadas=max(base.semanas_procesadas, nuevo.semanas_procesadas),
        )
        # Afinidad: merge con peso a nuevo
        merged.afinidad_emp_ws = dict(base.afinidad_emp_ws)
        for k, v in nuevo.afinidad_emp_ws.items():
            if k in merged.afinidad_emp_ws:
                old = merged.afinidad_emp_ws[k]
                # Sumar frecuencias, ponderar horas
                total_f = old.frecuencia + v.frecuencia
                merged.afinidad_emp_ws[k] = type(v)(
                    emp_id=v.emp_id, ws_id=v.ws_id, frecuencia=total_f,
                    horas_promedio=round(
                        (old.horas_promedio * old.frecuencia + v.horas_promedio * v.frecuencia) / max(1, total_f), 2
                    ),
                    dias_frecuentes=v.dias_frecuentes or old.dias_frecuentes,
                    horarios=list(set(old.horarios + v.horarios))[:10],
                    obs_frecuente=v.obs_frecuente,
                )
            else:
                merged.afinidad_emp_ws[k] = v

        # Horarios: nuevo tiene prioridad
        merged.horarios_ws = dict(base.horarios_ws)
        merged.horarios_ws.update(nuevo.horarios_ws)

        # Carga: nuevo tiene prioridad
        merged.carga_emp = dict(base.carga_emp)
        merged.carga_emp.update(nuevo.carga_emp)

        merged.obs_global = dict(base.obs_global)
        for k, v in nuevo.obs_global.items():
            merged.obs_global[k] = merged.obs_global.get(k, 0) + v

        return merged

    # ─────────────────────────────────────────
    # MODELO GETTER
    # ─────────────────────────────────────────

    @property
    def modelo(self) -> Optional[ModeloPatrones]:
        return self._modelo

    def cargar_o_entrenar(
        self,
        csv_path: str = None,
        fecha_inicio: Optional[date] = None,
        fecha_fin: Optional[date] = None,
    ) -> ModeloPatrones:
        """
        Intenta cargar modelo activo de BD.
        Si no hay, entrena desde CSV + BD.
        """
        # Intentar cargar de BD
        if self.cur and self._cargar_modelo_activo():
            self._log("Modelo activo cargado desde BD")
            return self._modelo

        # Entrenar
        if csv_path:
            self.entrenar_combinado(csv_path, fecha_inicio, fecha_fin)
        elif self.cur:
            self.entrenar_desde_bd(fecha_inicio, fecha_fin)
        else:
            self._log("Sin CSV ni BD: modelo vacío")
            self._modelo = ModeloPatrones()

        return self._modelo

    # ─────────────────────────────────────────
    # PERSISTENCIA
    # ─────────────────────────────────────────

    def guardar_modelo(self, nombre: str = "default", version: str = "4.0") -> str:
        """Guarda modelo en BD y lo marca como activo."""
        if not self.cur or not self._modelo:
            return ""
        model_id = str(uuid4())
        try:
            # Desactivar todos los activos
            self.cur.execute("""
                UPDATE "Management"."AIModels" SET "IsActive" = false WHERE "IsActive" = true
            """)
            # Serializar modelo
            model_data = pickle.dumps(self._modelo)
            metadata = json.dumps(self._modelo.to_dict(), ensure_ascii=False)
            self.cur.execute("""
                INSERT INTO "Management"."AIModels"
                    ("Id", "Name", "Version", "ModelData", "Metadata", "IsActive", "CreatedAt")
                VALUES (%s, %s, %s, %s, %s::jsonb, true, now())
            """, (model_id, nombre, version, model_data, metadata))
            self._log(f"Modelo guardado: {model_id} ({nombre} v{version})")
            return model_id
        except Exception as e:
            self._log(f"Error guardando modelo: {e}")
            return ""

    def _cargar_modelo_activo(self) -> bool:
        """Intenta cargar el modelo activo de BD."""
        if not self.cur:
            return False
        try:
            self.cur.execute("""
                SELECT "Id", "ModelData" FROM "Management"."AIModels"
                WHERE "IsActive" = true
                ORDER BY "CreatedAt" DESC LIMIT 1
            """)
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

    def registrar_training_history(
        self,
        model_id: str,
        data_start: Optional[date] = None,
        data_end: Optional[date] = None,
        notes: str = "",
        coverage_improvement: float = 0.0,
    ) -> None:
        """Registra historial de entrenamiento."""
        if not self.cur or not self._modelo:
            return
        try:
            self.cur.execute("""
                INSERT INTO "Management"."AITrainingHistory"
                    ("Id", "ModelId", "DataStartDate", "DataEndDate",
                     "RegistrosProcesados", "SemanasProcesadas",
                     "PatronesAfinidad", "PatronesHorario", "PatronesCarga",
                     "CoverageImprovement", "Notes", "CreatedAt")
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, now())
            """, (
                str(uuid4()), model_id, data_start, data_end,
                self._modelo.registros_procesados,
                self._modelo.semanas_procesadas,
                len(self._modelo.afinidad_emp_ws),
                len(self._modelo.horarios_ws),
                len(self._modelo.carga_emp),
                coverage_improvement, notes,
            ))
        except Exception as e:
            self._log(f"Error registrando history: {e}")

    def get_status(self) -> Dict[str, Any]:
        """Status del servicio."""
        if self._modelo:
            return {
                "entrenado": True,
                "modelo": self._modelo.to_dict(),
            }
        return {"entrenado": False}