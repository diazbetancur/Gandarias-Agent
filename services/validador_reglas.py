# services/validador_reglas.py
"""
HU 1.6 - Validador de reglas del schedule v5.0
==============================================
Alineado con las violaciones más importantes del query integral:
- RANGO_DE_TURNO_INVALIDO
- TURNO_MENOR_A_3_HORAS
- SOLAPAMIENTO_DE_TURNOS
- MENOS_DE_2_DIAS_DE_DESCANSO
- FUERA_DE_VENTANA_USER_SHIFT
- USUARIO_NO_HABILITADO_PARA_PUESTO
- EXCESO_DE_HORAS_SEMANALES
"""
from __future__ import annotations

import json
from collections import defaultdict
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from enum import Enum
from typing import Dict, List
from uuid import uuid4


class TipoViolacion(str, Enum):
    RANGO_INVALIDO = "RANGO_DE_TURNO_INVALIDO"
    TURNO_CORTO = "TURNO_MENOR_A_3_HORAS"
    SOLAPAMIENTO = "SOLAPAMIENTO_DE_TURNOS"
    DESCANSO_INSUFICIENTE = "MENOS_DE_2_DIAS_DE_DESCANSO"
    DESCANSO_ENTRE_TURNOS = "DESCANSO_ENTRE_TURNOS"
    FUERA_USERSHIFT = "FUERA_DE_VENTANA_USER_SHIFT"
    SIN_SKILL = "USUARIO_NO_HABILITADO_PARA_PUESTO"
    EXCESO_HORAS_SEMANALES = "EXCESO_DE_HORAS_SEMANALES"


class SeveridadViolacion(str, Enum):
    CRITICA = "CRITICA"
    ALTA = "ALTA"
    MEDIA = "MEDIA"
    BAJA = "BAJA"


REGLAS = {
    "min_duracion_bloque_horas": 3,
    "min_dias_descanso_semana": 2,
    "min_descanso_entre_turnos_horas": 9,
}


@dataclass
class Violacion:
    tipo: TipoViolacion
    severidad: SeveridadViolacion
    empleado_id: str
    empleado_nombre: str
    fecha: date | None
    detalle: str
    valor_actual: float
    valor_esperado: float
    workstation: str = ""
    bloque_inicio: str = ""
    bloque_fin: str = ""

    def to_dict(self):
        return {
            "tipo": self.tipo.value,
            "severidad": self.severidad.value,
            "empleado_id": self.empleado_id,
            "empleado_nombre": self.empleado_nombre,
            "fecha": self.fecha.isoformat() if self.fecha else None,
            "detalle": self.detalle,
            "valor_actual": self.valor_actual,
            "valor_esperado": self.valor_esperado,
            "workstation": self.workstation,
            "bloque_inicio": self.bloque_inicio,
            "bloque_fin": self.bloque_fin,
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
            self.cur.execute(
                f'''
                CREATE TABLE IF NOT EXISTS {self.table_name} (
                    "Id" uuid PRIMARY KEY DEFAULT gen_random_uuid(),
                    "Token" text NOT NULL,
                    "WeekStart" date,
                    "WeekEnd" date,
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
                '''
            )
        except Exception:
            pass

    @staticmethod
    def _merge(intervals):
        if not intervals:
            return []
        srt = sorted(intervals, key=lambda x: (x[0], x[1]))
        out = []
        cs, ce = srt[0][0], srt[0][1]
        for si, ei, *_ in srt[1:]:
            if si <= ce:
                ce = max(ce, ei)
            else:
                out.append((cs, ce))
                cs, ce = si, ei
        out.append((cs, ce))
        return out

    def validar(self, sched, emps=None):
        self._log("Iniciando validación de reglas...")
        violaciones: List[Violacion] = []
        emp_day = defaultdict(lambda: defaultdict(list))
        emp_names = {}
        emp_obj = {}
        emp_ids = set()
        dates_seen = set()

        for e in emps or []:
            emp_obj[str(e.id)] = e
            emp_names[str(e.id)] = getattr(e, "name", str(e.id))

        for d, pairs in (sched or {}).items():
            dates_seen.add(d)
            for emp, dm in pairs:
                if dm is None or getattr(dm, "wsid", None) is None:
                    continue
                eid = str(emp.id)
                emp_ids.add(eid)
                emp_names[eid] = getattr(emp, "name", eid)
                emp_obj[eid] = emp
                st, en = dm.start, dm.end
                if st is None or en is None:
                    violaciones.append(Violacion(TipoViolacion.RANGO_INVALIDO, SeveridadViolacion.CRITICA, eid, emp_names[eid], d, "Turno con hora nula", 0, 1, getattr(dm, 'wsname', '')))
                    continue
                si = st.hour * 60 + st.minute
                ei = en.hour * 60 + en.minute
                if ei <= si:
                    violaciones.append(Violacion(TipoViolacion.RANGO_INVALIDO, SeveridadViolacion.CRITICA, eid, emp_names[eid], d, "Hora fin <= hora inicio", 0, 1, getattr(dm, 'wsname', '')))
                    continue
                emp_day[eid][d].append((si, ei, getattr(dm, 'wsname', '') or '', str(getattr(dm, 'wsid', ''))))

                eobj = emp_obj.get(eid)
                if eobj and not eobj.can(getattr(dm, 'wsid', None)):
                    violaciones.append(Violacion(TipoViolacion.SIN_SKILL, SeveridadViolacion.CRITICA, eid, emp_names[eid], d, f"Usuario no habilitado para {getattr(dm, 'wsname', '')}", 0, 1, getattr(dm, 'wsname', '')))

                us_wins = getattr(eobj, 'user_shift_windows', {}).get(d.weekday(), []) if eobj else []
                if us_wins:
                    inside = False
                    for w_s, w_e in us_wins:
                        ws = w_s.hour * 60 + w_s.minute
                        we = w_e.hour * 60 + w_e.minute
                        if si >= ws and ei <= we:
                            inside = True
                            break
                    if not inside:
                        violaciones.append(Violacion(TipoViolacion.FUERA_USERSHIFT, SeveridadViolacion.ALTA, eid, emp_names[eid], d, f"Inicio fuera de UserShift en {getattr(dm, 'wsname', '')}", si / 60.0, 0, getattr(dm, 'wsname', '')))

        min_min = REGLAS["min_duracion_bloque_horas"] * 60
        for eid, days in emp_day.items():
            weekly_total = 0
            for d, ivs in days.items():
                merged = self._merge([(si, ei) for si, ei, *_ in ivs])
                weekly_total += sum(be - bs for bs, be in merged)
                for bs, be in merged:
                    if (be - bs) < min_min:
                        violaciones.append(Violacion(TipoViolacion.TURNO_CORTO, SeveridadViolacion.CRITICA, eid, emp_names[eid], d, f"Bloque {bs//60:02d}:{bs%60:02d}-{be//60:02d}:{be%60:02d} < 3h", (be - bs) / 60.0, REGLAS["min_duracion_bloque_horas"], bloque_inicio=f"{bs//60:02d}:{bs%60:02d}", bloque_fin=f"{be//60:02d}:{be%60:02d}"))

                # solapamientos reales por filas
                ivs_sorted = sorted(ivs, key=lambda x: (x[0], x[1]))
                for i in range(len(ivs_sorted) - 1):
                    a_s, a_e, a_ws, _ = ivs_sorted[i]
                    b_s, b_e, b_ws, _ = ivs_sorted[i + 1]
                    if a_e > b_s:
                        violaciones.append(Violacion(TipoViolacion.SOLAPAMIENTO, SeveridadViolacion.CRITICA, eid, emp_names[eid], d, f"Solapamiento entre {a_ws} y {b_ws}", 1, 0, workstation=f"{a_ws} / {b_ws}"))

            off = 7 - len(days)
            if off < REGLAS["min_dias_descanso_semana"]:
                any_day = min(days.keys()) if days else None
                violaciones.append(Violacion(TipoViolacion.DESCANSO_INSUFICIENTE, SeveridadViolacion.CRITICA, eid, emp_names[eid], any_day, f"Solo {off} días de descanso", off, REGLAS["min_dias_descanso_semana"]))

            eobj = emp_obj.get(eid)
            limit_fn = getattr(eobj, 'weekly_hours_limit', None)
            lim = limit_fn() if callable(limit_fn) else None
            if lim and weekly_total > lim:
                violaciones.append(Violacion(TipoViolacion.EXCESO_HORAS_SEMANALES, SeveridadViolacion.ALTA, eid, emp_names[eid], None, f"{weekly_total/60:.1f}h > {lim/60:.1f}h semanales", weekly_total / 60.0, lim / 60.0))

            sd = sorted(days.keys())
            for i in range(len(sd) - 1):
                if (sd[i + 1] - sd[i]).days != 1:
                    continue
                prev_blocks = self._merge([(si, ei) for si, ei, *_ in days[sd[i]]])
                next_blocks = self._merge([(si, ei) for si, ei, *_ in days[sd[i + 1]]])
                if not prev_blocks or not next_blocks:
                    continue
                rest = (24 * 60 - max(be for _, be in prev_blocks)) + min(bs for bs, _ in next_blocks)
                if rest < REGLAS["min_descanso_entre_turnos_horas"] * 60:
                    violaciones.append(Violacion(TipoViolacion.DESCANSO_ENTRE_TURNOS, SeveridadViolacion.ALTA, eid, emp_names[eid], sd[i], f"Solo {rest/60:.1f}h entre días consecutivos", rest / 60.0, REGLAS["min_descanso_entre_turnos_horas"]))

        cr = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.CRITICA)
        al = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.ALTA)
        me = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.MEDIA)
        ba = sum(1 for v in violaciones if v.severidad == SeveridadViolacion.BAJA)
        res = ResultadoValidacion(
            total_violaciones=len(violaciones),
            violaciones_criticas=cr,
            violaciones_altas=al,
            violaciones_medias=me,
            violaciones_bajas=ba,
            violaciones=violaciones,
            empleados_validados=len(emp_ids),
            dias_validados=len(dates_seen),
            reglas_verificadas=[
                "RANGO_INVALIDO",
                "MIN_3H",
                "SOLAPAMIENTO",
                "DESCANSO_2_DIAS",
                "DESCANSO_ENTRE_TURNOS",
                "USERSHIFT",
                "SKILLS",
                "HORAS_SEMANALES",
            ],
            schedule_valido=(cr == 0 and al == 0),
        )
        self._log(f"Resultado: {res.total_violaciones} violaciones ({cr}C {al}A {me}M {ba}B)")
        return res

    def guardar(self, resultado, token, week_start, week_end, is_post_ai=True):
        if not self.cur:
            return 0
        try:
            self.cur.execute(
                f'''
                INSERT INTO {self.table_name}
                  ("Id","Token","WeekStart","WeekEnd","TotalViolaciones","ViolacionesCriticas",
                   "ViolacionesAltas","ViolacionesMedias","ViolacionesBajas",
                   "EmpleadosValidados","DiasValidados","ScheduleValido","IsPostAi","Detalle","CreatedAt")
                VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s::jsonb,%s)
                ''',
                (
                    str(uuid4()), token, week_start, week_end,
                    resultado.total_violaciones, resultado.violaciones_criticas, resultado.violaciones_altas,
                    resultado.violaciones_medias, resultado.violaciones_bajas,
                    resultado.empleados_validados, resultado.dias_validados,
                    resultado.schedule_valido, bool(is_post_ai),
                    json.dumps(resultado.to_dict(), ensure_ascii=False), datetime.utcnow(),
                ),
            )
            return 1
        except Exception as e:
            self._log(f"Error guardando: {e}")
            return 0

    def validar_y_guardar(self, sched, token, week_start, week_end, emps=None, is_post_ai=True):
        r = self.validar(sched, emps)
        self.guardar(r, token, week_start, week_end, is_post_ai)
        return r
