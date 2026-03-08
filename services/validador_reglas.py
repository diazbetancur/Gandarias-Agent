# services/validador_reglas.py
"""
HU 1.6 - Validador de Reglas del Schedule
==========================================
Verifica que el schedule cumple TODAS las reglas duras del PDF.
Auto-crea la tabla si no existe.
"""
from __future__ import annotations
import json
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, date, time, timedelta
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple
from uuid import uuid4


class TipoViolacion(str, Enum):
    TURNO_CORTO = "TURNO_CORTO"
    EXCESO_HORAS_DIA = "EXCESO_HORAS_DIA"
    EXCESO_BLOQUES_DIA = "EXCESO_BLOQUES_DIA"
    DESCANSO_INSUFICIENTE = "DESCANSO_INSUFICIENTE"
    DESCANSO_ENTRE_TURNOS = "DESCANSO_ENTRE_TURNOS"


class SeveridadViolacion(str, Enum):
    CRITICA = "CRITICA"
    ALTA = "ALTA"
    MEDIA = "MEDIA"
    BAJA = "BAJA"


REGLAS = {
    "min_duracion_bloque_horas": 3,
    "max_horas_dia": 10,
    "max_bloques_dia": 2,
    "min_dias_descanso_semana": 2,
    "min_descanso_entre_turnos_horas": 9,
}


@dataclass
class Violacion:
    tipo: TipoViolacion
    severidad: SeveridadViolacion
    empleado_id: str
    empleado_nombre: str
    fecha: date
    detalle: str
    valor_actual: float
    valor_esperado: float
    workstation: str = ""
    bloque_inicio: str = ""
    bloque_fin: str = ""

    def to_dict(self):
        return {
            "tipo": self.tipo.value, "severidad": self.severidad.value,
            "empleado_id": self.empleado_id, "empleado_nombre": self.empleado_nombre,
            "fecha": self.fecha.isoformat(), "detalle": self.detalle,
            "valor_actual": self.valor_actual, "valor_esperado": self.valor_esperado,
            "workstation": self.workstation,
            "bloque_inicio": self.bloque_inicio, "bloque_fin": self.bloque_fin,
        }


@dataclass
class ResultadoValidacion:
    total_violaciones: int
    violaciones_criticas: int
    violaciones_altas: int
    violaciones_medias: int
    violaciones_bajas: int
    violaciones: List[Violacion]
    empleados_validados: int
    dias_validados: int
    reglas_verificadas: List[str]
    schedule_valido: bool

    def to_dict(self):
        return {
            "total_violaciones": self.total_violaciones,
            "violaciones_criticas": self.violaciones_criticas,
            "violaciones_altas": self.violaciones_altas,
            "violaciones_medias": self.violaciones_medias,
            "violaciones_bajas": self.violaciones_bajas,
            "empleados_validados": self.empleados_validados,
            "dias_validados": self.dias_validados,
            "reglas_verificadas": self.reglas_verificadas,
            "schedule_valido": self.schedule_valido,
            "violaciones": [v.to_dict() for v in self.violaciones],
        }


class ValidadorReglasService:
    def __init__(self, cursor=None, table_name='"Management"."ScheduleRuleValidations"', debug=True):
        self.cur = cursor
        self.table_name = table_name
        self.debug = debug
        self._ensure_table()

    def _log(self, msg):
        if self.debug:
            print(f"[HU1.6] {msg}")

    def _ensure_table(self):
        if not self.cur:
            return
        try:
            self.cur.execute(f"""
                CREATE TABLE IF NOT EXISTS {self.table_name} (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "Token" text NOT NULL,
                    "WeekStart" date, "WeekEnd" date,
                    "TotalViolaciones" integer NOT NULL DEFAULT 0,
                    "ViolacionesCriticas" integer NOT NULL DEFAULT 0,
                    "ViolacionesAltas" integer NOT NULL DEFAULT 0,
                    "ViolacionesMedias" integer NOT NULL DEFAULT 0,
                    "ViolacionesBajas" integer NOT NULL DEFAULT 0,
                    "EmpleadosValidados" integer NOT NULL DEFAULT 0,
                    "DiasValidados" integer NOT NULL DEFAULT 0,
                    "ScheduleValido" boolean NOT NULL DEFAULT true,
                    "IsPostAi" boolean NOT NULL DEFAULT false,
                    "Detalle" jsonb,
                    "CreatedAt" timestamp without time zone DEFAULT now()
                );
            """)
        except Exception:
            pass

    def _merge(self, intervals):
        if not intervals:
            return []
        srt = sorted(intervals, key=lambda x: (x[0], x[1]))
        blocks = []
        cs, ce = srt[0][0], srt[0][1]
        for si, ei, *_ in srt[1:]:
            if si <= ce + 15:
                ce = max(ce, ei)
            else:
                blocks.append((cs, ce))
                cs, ce = si, ei
        blocks.append((cs, ce))
        return blocks

    def validar(self, sched, emps=None):
        self._log("Iniciando validacion de reglas...")
        violaciones = []
        emp_ids, dates_seen = set(), set()
        emp_day = defaultdict(lambda: defaultdict(list))
        emp_names = {}

        for d, pairs in (sched or {}).items():
            dates_seen.add(d)
            for emp, dm in pairs:
                if dm is None or getattr(dm, 'wsid', None) is None:
                    continue
                eid = str(emp.id)
                emp_ids.add(eid)
                emp_names[eid] = getattr(emp, 'name', eid)
                st, en = dm.start, dm.end
                si = st.hour * 60 + st.minute
                ei = en.hour * 60 + en.minute
                if ei <= si:
                    ei += 24 * 60
                emp_day[eid][d].append((si, ei, getattr(dm, 'wsname', '') or ''))

        min_min = REGLAS["min_duracion_bloque_horas"] * 60
        for eid, days in emp_day.items():
            for d, ivs in days.items():
                for bs, be in self._merge(ivs):
                    if (be - bs) < min_min:
                        violaciones.append(Violacion(
                            TipoViolacion.TURNO_CORTO, SeveridadViolacion.ALTA,
                            eid, emp_names.get(eid, eid), d,
                            f"Bloque {bs//60:02d}:{bs%60:02d}-{be//60:02d}:{be%60:02d} = {(be-bs)/60:.1f}h < 3h",
                            (be-bs)/60, float(REGLAS["min_duracion_bloque_horas"]),
                            bloque_inicio=f"{bs//60:02d}:{bs%60:02d}", bloque_fin=f"{be//60:02d}:{be%60:02d}"))

        max_min = REGLAS["max_horas_dia"] * 60
        for eid, days in emp_day.items():
            for d, ivs in days.items():
                total = sum(be-bs for bs, be in self._merge(ivs))
                if total > max_min:
                    violaciones.append(Violacion(
                        TipoViolacion.EXCESO_HORAS_DIA, SeveridadViolacion.CRITICA,
                        eid, emp_names.get(eid, eid), d,
                        f"Total {total/60:.1f}h > {REGLAS['max_horas_dia']}h", total/60, float(REGLAS["max_horas_dia"])))

        for eid, days in emp_day.items():
            for d, ivs in days.items():
                nb = len(self._merge(ivs))
                if nb > REGLAS["max_bloques_dia"]:
                    violaciones.append(Violacion(
                        TipoViolacion.EXCESO_BLOQUES_DIA, SeveridadViolacion.MEDIA,
                        eid, emp_names.get(eid, eid), d,
                        f"{nb} bloques > {REGLAS['max_bloques_dia']}", float(nb), float(REGLAS["max_bloques_dia"])))

        for eid, days in emp_day.items():
            off = 7 - len(days)
            if off < REGLAS["min_dias_descanso_semana"]:
                violaciones.append(Violacion(
                    TipoViolacion.DESCANSO_INSUFICIENTE, SeveridadViolacion.CRITICA,
                    eid, emp_names.get(eid, eid), min(days.keys()),
                    f"{len(days)} dias, solo {off} descanso", float(off), float(REGLAS["min_dias_descanso_semana"])))

        for eid, days in emp_day.items():
            sd = sorted(days.keys())
            for i in range(len(sd)-1):
                if (sd[i+1]-sd[i]).days != 1:
                    continue
                b1, b2 = self._merge(days[sd[i]]), self._merge(days[sd[i+1]])
                if not b1 or not b2:
                    continue
                rest = (24*60 - max(be for _, be in b1)) + min(bs for bs, _ in b2)
                if rest < REGLAS["min_descanso_entre_turnos_horas"]*60:
                    violaciones.append(Violacion(
                        TipoViolacion.DESCANSO_ENTRE_TURNOS, SeveridadViolacion.ALTA,
                        eid, emp_names.get(eid, eid), sd[i],
                        f"Solo {rest/60:.1f}h entre {sd[i]} y {sd[i+1]}", rest/60, float(REGLAS["min_descanso_entre_turnos_horas"])))

        cr = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.CRITICA)
        al = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.ALTA)
        me = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.MEDIA)
        ba = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.BAJA)

        r = ResultadoValidacion(
            len(violaciones), cr, al, me, ba, violaciones,
            len(emp_ids), len(dates_seen),
            ["2.1-MIN_3H", "2.2-MAX_BLOQUES", "2.3-MAX_HORAS", "2.3-DESCANSO_SEMANAL", "2.3-DESCANSO_ENTRE_TURNOS"],
            cr == 0 and al == 0)
        self._log(f"Resultado: {r.total_violaciones} violaciones ({cr}C {al}A {me}M {ba}B) | {'VALIDO' if r.schedule_valido else 'INVALIDO'}")
        return r

    def guardar(self, resultado, token, week_start, week_end, is_post_ai=True):
        if not self.cur:
            return 0
        try:
            self.cur.execute(f"""
                INSERT INTO {self.table_name}
                  ("Id","Token","WeekStart","WeekEnd","TotalViolaciones","ViolacionesCriticas",
                   "ViolacionesAltas","ViolacionesMedias","ViolacionesBajas",
                   "EmpleadosValidados","DiasValidados","ScheduleValido","IsPostAi","Detalle","CreatedAt")
                VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s::jsonb,%s)
            """, (str(uuid4()), token, week_start, week_end,
                  resultado.total_violaciones, resultado.violaciones_criticas, resultado.violaciones_altas,
                  resultado.violaciones_medias, resultado.violaciones_bajas,
                  resultado.empleados_validados, resultado.dias_validados,
                  resultado.schedule_valido, bool(is_post_ai),
                  json.dumps(resultado.to_dict(), ensure_ascii=False), datetime.utcnow()))
            return 1
        except Exception as e:
            self._log(f"Error guardando: {e}")
            return 0

    def validar_y_guardar(self, sched, token, week_start, week_end, emps=None, is_post_ai=True):
        r = self.validar(sched, emps)
        self.guardar(r, token, week_start, week_end, is_post_ai)
        return r