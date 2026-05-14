# services/ai_scheduler.py
"""
Motor de IA para Agendamiento – Gandarias v5.0
================================================
Mejoras clave:
  - Híbridos nativos para demandas con EffortRequired = 0.5
  - Validación dura antes de asignar (incluye horas semanales)
  - Prioridad a cobertura con piso objetivo configurable
  - Scorer enriquecido con quality/suggestions/violaciones/híbridos históricos
  - Mantiene aprendizaje base desde CSV / BD
"""

from __future__ import annotations

import csv
import logging
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from datetime import date, datetime, time, timedelta
from typing import Any, Dict, List, Optional, Set, Tuple
from uuid import uuid4

logger = logging.getLogger("ai_scheduler")

REGLAS_DURAS_DEFAULTS = {
    "min_duracion_turno_horas": 3,
    "min_descanso_entre_turnos_horas": 9,
    "min_gap_split_horas": 3,
    "max_horas_por_dia": 9,
    "dias_descanso_semana": 2,
    "max_dias_trabajo_semana": 5,
    "max_bloques_por_dia": 2,
}


def _t2m(t: time) -> int:
    return t.hour * 60 + t.minute


def _m2t(m: int) -> time:
    m = max(0, min(m, 24 * 60 - 1))
    return time(m // 60, m % 60)


def _end_eff(t: time) -> time:
    return t if t != time(0, 0) else time(23, 59)


def _end_min(t: time) -> int:
    """
    Para cálculos internos, 23:59 y 00:00 al final de día se tratan como 24:00.
    """
    if t == time(0, 0) or t == time(23, 59):
        return 24 * 60
    return _t2m(t)


def _seg_min(start: time, end: time) -> int:
    return max(0, _end_min(end) - _t2m(start))


def _merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    srt = sorted(intervals)
    merged = [list(srt[0])]
    for s, e in srt[1:]:
        if s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    return [(a, b) for a, b in merged]


def _has_overlap(intervals: List[Tuple[int, int]], s: int, e: int) -> bool:
    for a, b in intervals:
        if not (e <= a or b <= s):
            return True
    return False


def _uid() -> str:
    return str(uuid4())


# ═══════════════════════════════════════════════════════════════════
# MODELO DE PATRONES
# ═══════════════════════════════════════════════════════════════════


@dataclass
class PatronEmpWS:
    emp_id: str
    ws_id: str
    frecuencia: int = 0
    horas_promedio: float = 0.0
    dias_frecuentes: List[int] = field(default_factory=list)
    horarios: List[Tuple[str, str]] = field(default_factory=list)
    obs_frecuente: str = "BT"


@dataclass
class PatronHorarioWS:
    ws_id: str
    dow: int
    inicio_tipico_min: int = 720
    fin_tipico_min: int = 1380
    frecuencia: int = 0
    duracion_prom_min: float = 0.0


@dataclass
class PatronCarga:
    emp_id: str
    horas_sem_prom: float = 0.0
    dias_trabajo_prom: float = 5.0
    dias_descanso_freq: List[int] = field(default_factory=list)


@dataclass
class ModeloPatrones:
    version: str = "5.0"
    fecha_entrenamiento: str = ""
    registros_procesados: int = 0
    semanas_procesadas: int = 0
    afinidad_emp_ws: Dict = field(default_factory=dict)
    horarios_ws: Dict = field(default_factory=dict)
    carga_emp: Dict = field(default_factory=dict)
    obs_global: Dict = field(default_factory=dict)

    def to_dict(self):
        return {
            "version": self.version,
            "fecha_entrenamiento": self.fecha_entrenamiento,
            "registros_procesados": self.registros_procesados,
            "semanas_procesadas": self.semanas_procesadas,
            "patrones_afinidad": len(self.afinidad_emp_ws),
            "patrones_horario": len(self.horarios_ws),
            "patrones_carga": len(self.carga_emp),
            "obs_global_keys": len(self.obs_global),
        }


# ═══════════════════════════════════════════════════════════════════
# EXTRACTOR DE PATRONES
# ═══════════════════════════════════════════════════════════════════


class ExtractorPatrones:
    def __init__(self, debug: bool = True):
        self.debug = debug

    def _log(self, msg: str):
        if self.debug:
            print(f"[AI-EXTRACT] {msg}")

    def extraer_de_csv(self, csv_path: str) -> ModeloPatrones:
        self._log(f"Cargando histórico desde {csv_path}")
        registros = []
        with open(csv_path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                if str(row.get("IsDeleted", "false")).lower() == "true":
                    continue
                if not row.get("WorkstationId") or not row.get("StartTime"):
                    continue
                registros.append(
                    {
                        "date": row.get("Date"),
                        "emp_id": row.get("UserId"),
                        "ws_id": row.get("WorkstationId"),
                        "start": row.get("StartTime"),
                        "end": row.get("EndTime"),
                        "obs": row.get("Observation", "") or "",
                    }
                )
        self._log(f"Cargados {len(registros)} registros")
        return self._procesar(registros)

    def extraer_de_bd(self, cursor, fecha_ini=None, fecha_fin=None) -> ModeloPatrones:
        self._log("Cargando histórico desde BD")
        q = """
            SELECT s."Date", s."UserId"::text, s."WorkstationId"::text,
                   s."StartTime", s."EndTime", COALESCE(s."Observation", '')
            FROM "Management"."Schedules" s
            WHERE COALESCE(s."IsDeleted", false) = false
              AND s."WorkstationId" IS NOT NULL
              AND s."StartTime" IS NOT NULL
              AND s."EndTime" IS NOT NULL
        """
        params = []
        if fecha_ini:
            q += ' AND s."Date" >= %s'
            params.append(fecha_ini)
        if fecha_fin:
            q += ' AND s."Date" <= %s'
            params.append(fecha_fin)
        q += ' ORDER BY s."Date", s."UserId", s."StartTime"'
        cursor.execute(q, params)
        registros = [
            {
                "date": str(r[0]),
                "emp_id": str(r[1]) if r[1] else None,
                "ws_id": str(r[2]) if r[2] else None,
                "start": str(r[3]) if r[3] else None,
                "end": str(r[4]) if r[4] else None,
                "obs": r[5] or "",
            }
            for r in cursor.fetchall()
        ]
        self._log(f"Cargados {len(registros)} registros BD")
        return self._procesar(registros)

    @staticmethod
    def _parse_time_str(s: str) -> Optional[int]:
        if not s:
            return None
        try:
            parts = s.strip().split(":")
            h, m = int(parts[0]), int(parts[1])
            if h >= 24:
                h, m = 23, 59
            return h * 60 + m
        except Exception:
            return None

    @staticmethod
    def _parse_date(s: str) -> Optional[date]:
        try:
            return datetime.strptime(s.strip()[:10], "%Y-%m-%d").date()
        except Exception:
            return None

    def _procesar(self, registros) -> ModeloPatrones:
        modelo = ModeloPatrones(
            fecha_entrenamiento=datetime.now().isoformat(),
            registros_procesados=len(registros),
        )
        afinidad_acc = defaultdict(list)
        horario_acc = defaultdict(list)
        carga_acc = defaultdict(lambda: {"mins_by_week": defaultdict(int), "days_by_week": defaultdict(set)})
        obs_counter = Counter()
        semanas = set()

        for reg in registros:
            emp_id, ws_id = reg.get("emp_id"), reg.get("ws_id")
            if not emp_id or not ws_id:
                continue
            d = self._parse_date(reg.get("date", ""))
            s_min = self._parse_time_str(reg.get("start", ""))
            e_min = self._parse_time_str(reg.get("end", ""))
            if d is None or s_min is None or e_min is None:
                continue
            dur = e_min - s_min
            if dur <= 0:
                dur += 1440
            if dur <= 0 or dur > 1440:
                continue
            dow = d.weekday()
            wk = f"{d.year}-W{d.isocalendar()[1]:02d}"
            semanas.add(wk)
            afinidad_acc[(emp_id, ws_id)].append(
                {
                    "dow": dow,
                    "start": s_min,
                    "end": e_min,
                    "dur": dur,
                    "obs": reg.get("obs", ""),
                }
            )
            horario_acc[(ws_id, dow)].append((s_min, e_min))
            carga_acc[emp_id]["mins_by_week"][wk] += dur
            carga_acc[emp_id]["days_by_week"][wk].add(d)
            obs_counter[reg.get("obs", "") or ""] += 1

        modelo.semanas_procesadas = len(semanas)
        modelo.obs_global = dict(obs_counter)

        for (emp_id, ws_id), items in afinidad_acc.items():
            dow_c = Counter(it["dow"] for it in items)
            obs_c = Counter(it["obs"] for it in items)
            h_prom = sum(it["dur"] for it in items) / len(items) / 60.0
            horarios = list(
                {
                    (
                        f"{it['start']//60:02d}:{it['start']%60:02d}",
                        f"{it['end']//60:02d}:{it['end']%60:02d}",
                    )
                    for it in items
                }
            )[:10]
            modelo.afinidad_emp_ws[(emp_id, ws_id)] = PatronEmpWS(
                emp_id=emp_id,
                ws_id=ws_id,
                frecuencia=len(items),
                horas_promedio=round(h_prom, 2),
                dias_frecuentes=sorted(dow_c, key=dow_c.get, reverse=True)[:5],
                horarios=horarios,
                obs_frecuente=obs_c.most_common(1)[0][0] if obs_c else "BT",
            )

        for (ws_id, dow), times in horario_acc.items():
            starts = [t[0] for t in times]
            ends = [t[1] for t in times]
            durs = [max(0, e - s) if e > s else max(0, e + 1440 - s) for s, e in times]
            modelo.horarios_ws[(ws_id, dow)] = PatronHorarioWS(
                ws_id=ws_id,
                dow=dow,
                inicio_tipico_min=int(sum(starts) / len(starts)) if starts else 720,
                fin_tipico_min=int(sum(ends) / len(ends)) if ends else 1380,
                frecuencia=len(times),
                duracion_prom_min=sum(durs) / len(durs) if durs else 0,
            )

        for emp_id, data in carga_acc.items():
            weeks = data["mins_by_week"]
            days = data["days_by_week"]
            if not weeks:
                continue
            h_sem = [v / 60.0 for v in weeks.values()]
            d_sem = [len(v) for v in days.values()]
            all_dows = Counter()
            for wk, day_set in days.items():
                for dd in day_set:
                    all_dows[dd.weekday()] += 1
            n_w = len(weeks)
            d_desc = [dow for dow in range(7) if all_dows.get(dow, 0) < n_w * 0.3]
            modelo.carga_emp[emp_id] = PatronCarga(
                emp_id=emp_id,
                horas_sem_prom=round(sum(h_sem) / len(h_sem), 1),
                dias_trabajo_prom=round(sum(d_sem) / len(d_sem), 1),
                dias_descanso_freq=sorted(d_desc),
            )

        self._log(
            f"Modelo: {modelo.semanas_procesadas} semanas, "
            f"{len(modelo.afinidad_emp_ws)} afinidades, "
            f"{len(modelo.horarios_ws)} pat.horario, "
            f"{len(modelo.carga_emp)} pat.carga"
        )
        return modelo


# ═══════════════════════════════════════════════════════════════════
# ESTADO / HÍBRIDOS
# ═══════════════════════════════════════════════════════════════════


@dataclass
class EstadoEmpleado:
    emp_id: str
    minutos_semana: int = 0
    dias_trabajados: Set[date] = field(default_factory=set)
    minutos_por_dia: Dict[date, int] = field(default_factory=dict)
    intervalos_por_dia: Dict[date, List[Tuple[int, int]]] = field(default_factory=lambda: defaultdict(list))
    asignaciones: List[Tuple[date, str, int, int]] = field(default_factory=list)

    def registrar(self, d, ws_id, s_min, e_min):
        dur = max(0, e_min - s_min)
        self.minutos_semana += dur
        self.dias_trabajados.add(d)
        self.minutos_por_dia[d] = self.minutos_por_dia.get(d, 0) + dur
        self.intervalos_por_dia[d].append((s_min, e_min))
        self.asignaciones.append((d, ws_id, s_min, e_min))

    def desregistrar(self, d, ws_id, s_min, e_min):
        dur = max(0, e_min - s_min)
        self.minutos_semana = max(0, self.minutos_semana - dur)
        self.minutos_por_dia[d] = max(0, self.minutos_por_dia.get(d, 0) - dur)
        if (s_min, e_min) in self.intervalos_por_dia.get(d, []):
            self.intervalos_por_dia[d].remove((s_min, e_min))
        if not self.intervalos_por_dia.get(d):
            self.dias_trabajados.discard(d)
        try:
            self.asignaciones.remove((d, ws_id, s_min, e_min))
        except ValueError:
            pass


# ═══════════════════════════════════════════════════════════════════
# CANDIDATE PLAN (ScheduleGapFillingPass)
# ═══════════════════════════════════════════════════════════════════


@dataclass
class CandidatePlan:
    """Plan candidato generado por ScheduleGapFillingPass."""

    emp: Any  # objeto empleado
    d: date  # día del plan
    plan_type: str  # "EXTEND" | "SPLIT" | "NEW"
    chain: List  # demandas a agregar (lista de Demand)
    chain_s: int  # start_min de la cadena
    chain_e: int  # end_min de la cadena
    chain_dur: int  # duración de la cadena en minutos
    score: float = 0.0  # calculado en _score_gap_plan


# ═══════════════════════════════════════════════════════════════════
# VALIDADOR DE REGLAS DURAS
# ═══════════════════════════════════════════════════════════════════


class ValidadorReglasDuras:
    def __init__(self, reglas=None):
        self.reglas = reglas or dict(REGLAS_DURAS_DEFAULTS)

    def _usershift_ok(self, emp, d, start_t: time, end_t: time, overrides=None) -> bool:
        overrides = overrides or set()
        if (str(emp.id), d) in overrides:
            return True
        us_wins = getattr(emp, "user_shift_windows", {}).get(d.weekday(), [])
        if not us_wins:
            return True
        end_eff = _end_eff(end_t)
        for w_s, w_e in us_wins:
            w_end = _end_eff(w_e)
            if start_t >= w_s and end_eff <= w_end:
                return True
        return False

    def _weekly_hours_ok(self, emp, estado_emp: EstadoEmpleado, dur_min: int) -> bool:
        limit_fn = getattr(emp, "weekly_hours_limit", None)
        if not callable(limit_fn):
            return True
        lim = limit_fn()
        if not lim:
            return True
        return (estado_emp.minutos_semana + dur_min) <= lim

    def _post_interval_checks(
        self, d, estado_emp: EstadoEmpleado, s_new: int, e_new: int, allow_short_block_provisional: bool = True
    ):
        if _has_overlap(estado_emp.intervalos_por_dia.get(d, []), s_new, e_new):
            return False, "SOLAPAMIENTO"

        max_bloques = self.reglas.get("max_bloques_por_dia", 2)
        min_gap_split = self.reglas.get("min_gap_split_horas", 3) * 60
        ivs = list(estado_emp.intervalos_por_dia.get(d, []))
        ivs.append((s_new, e_new))
        bloques = _merge_intervals(ivs)
        if len(bloques) > max_bloques:
            return False, "MAX_BLOQUES"

        min_turno = self.reglas.get("min_duracion_turno_horas", 3) * 60
        for bs, be in bloques:
            if bs <= s_new and e_new <= be:
                if (be - bs) < min_turno:
                    if not allow_short_block_provisional:
                        # Modo estricto (fase final): rechazar siempre si el bloque
                        # resultante queda < min_turno, sin excepción provisional.
                        return False, "BLOQUE_CORTO_FINAL"
                    # Modo constructivo: solo rechazar si es la primera asignación
                    # del día (podría crecer con futuras asignaciones).
                    existing_day_min = sum(max(0, ie - ib) for ib, ie in estado_emp.intervalos_por_dia.get(d, []))
                    if existing_day_min == 0:
                        return False, "BLOQUE_CORTO_PROVISIONAL"
                    # Ya tiene algo asignado hoy — se tolera provisionalmente
                break

        if len(bloques) >= 2:
            for i in range(len(bloques) - 1):
                gap = bloques[i + 1][0] - bloques[i][1]
                if gap < min_gap_split:
                    return False, "GAP_SPLIT_INSUFICIENTE"

        min_desc_min = self.reglas.get("min_descanso_entre_turnos_horas", 9) * 60
        d_prev = d - timedelta(days=1)
        if d_prev in estado_emp.intervalos_por_dia and estado_emp.intervalos_por_dia[d_prev]:
            last_end = max(e for _, e in estado_emp.intervalos_por_dia[d_prev])
            rest = (1440 - last_end) + s_new
            if rest < min_desc_min:
                return False, "DESC_ENTRE_TURNOS"
        d_next = d + timedelta(days=1)
        if d_next in estado_emp.intervalos_por_dia and estado_emp.intervalos_por_dia[d_next]:
            first_start = min(s for s, _ in estado_emp.intervalos_por_dia[d_next])
            rest = (1440 - e_new) + first_start
            if rest < min_desc_min:
                return False, "DESC_ENTRE_TURNOS"
        return True, ""

    def puede_asignar(
        self, emp, dm, d, estado_emp: EstadoEmpleado, overrides=None, allow_short_block_provisional: bool = True
    ):
        overrides = overrides or set()
        if not emp.can(dm.wsid):
            return False, "SIN_SKILL"
        if emp.off(d) or emp.absent_day(d):
            return False, "DIA_LIBRE"
        if not emp.available(d, dm.start, dm.end):
            return False, "FUERA_VENTANA"
        if not self._usershift_ok(emp, d, dm.start, dm.end, overrides):
            return False, "FUERA_USERSHIFT_WINDOW"

        max_dias = self.reglas.get("max_dias_trabajo_semana", 5)
        if d not in estado_emp.dias_trabajados and len(estado_emp.dias_trabajados) >= max_dias:
            return False, "MAX_DIAS"

        dur = _seg_min(dm.start, dm.end)
        if dur <= 0:
            return False, "RANGO_INVALIDO"

        max_h = self.reglas.get("max_horas_por_dia", 9) * 60
        if estado_emp.minutos_por_dia.get(d, 0) + dur > max_h:
            return False, "MAX_HORAS_DIA"
        if not self._weekly_hours_ok(emp, estado_emp, dur):
            return False, "MAX_HORAS_SEMANALES"

        return self._post_interval_checks(
            d,
            estado_emp,
            _t2m(dm.start),
            _end_min(dm.end),
            allow_short_block_provisional=allow_short_block_provisional,
        )

    def puede_asignar_hibrido(
        self, emp, grp, d, estado_emp: EstadoEmpleado, overrides=None, allow_short_block_provisional: bool = True
    ):
        overrides = overrides or set()
        if not emp.can(grp.wsid_a) or not emp.can(grp.wsid_b):
            return False, "SIN_SKILL_HYB"
        if emp.off(d) or emp.absent_day(d):
            return False, "DIA_LIBRE"
        if not emp.available(d, grp.start, grp.end):
            return False, "FUERA_VENTANA"
        if not self._usershift_ok(emp, d, grp.start, grp.end, overrides):
            return False, "FUERA_USERSHIFT_WINDOW"

        max_dias = self.reglas.get("max_dias_trabajo_semana", 5)
        if d not in estado_emp.dias_trabajados and len(estado_emp.dias_trabajados) >= max_dias:
            return False, "MAX_DIAS"

        dur = _seg_min(grp.start, grp.end)
        if dur <= 0:
            return False, "RANGO_INVALIDO"
        if dur < self.reglas.get("min_duracion_turno_horas", 3) * 60:
            return False, "TURNO_CORTO"

        max_h = self.reglas.get("max_horas_por_dia", 9) * 60
        if estado_emp.minutos_por_dia.get(d, 0) + dur > max_h:
            return False, "MAX_HORAS_DIA"
        if not self._weekly_hours_ok(emp, estado_emp, dur):
            return False, "MAX_HORAS_SEMANALES"

        return self._post_interval_checks(
            d,
            estado_emp,
            _t2m(grp.start),
            _end_min(grp.end),
            allow_short_block_provisional=allow_short_block_provisional,
        )


# ═══════════════════════════════════════════════════════════════════
# SCORER
# ═══════════════════════════════════════════════════════════════════


class ScorerCandidatos:
    def __init__(self, modelo: ModeloPatrones):
        self.modelo = modelo or ModeloPatrones()
        self.suggestion_hints = {}  # Se inyecta desde generate_ai
        self._emp_name_map = {}  # Se inyecta desde generate_ai

    def _weekly_deficit_score(self, emp, estado) -> float:
        """Score basado en cuántas horas le FALTAN para llegar a su límite.
        1.0 = no tiene nada asignado (máxima prioridad)
        0.0 = ya alcanzó su límite (no debería recibir más)"""
        limit_fn = getattr(emp, "weekly_hours_limit", None)
        if not callable(limit_fn):
            return 0.5
        try:
            hired_min = int(limit_fn() or 0)
        except Exception:
            hired_min = 0
        if hired_min <= 0:
            return 0.0
        assigned_min = int(getattr(estado, "minutos_semana", 0) or 0)
        deficit = max(0, hired_min - assigned_min)
        return max(0.0, min(1.0, deficit / hired_min))

    def _balance_score(self, estado, prom_min_sem) -> float:
        """Score de BALANCE/EQUIDAD — el componente más importante.
        Penaliza fuertemente a empleados que ya tienen mucha carga vs el promedio.
        Premia fuertemente a empleados con poca carga.

        ratio=0.0 (sin horas) → score=1.0
        ratio=0.5 (mitad del promedio) → score=0.85
        ratio=1.0 (en el promedio) → score=0.5
        ratio=1.5 (150% del promedio) → score=0.1
        ratio=2.0+ (doble del promedio) → score=0.0
        """
        if prom_min_sem <= 0:
            return 1.0
        ratio = estado.minutos_semana / prom_min_sem
        if ratio <= 0:
            return 1.0
        if ratio >= 2.0:
            return 0.0
        # Curva cuadrática que cae rápido después del promedio
        return max(0.0, min(1.0, 1.0 - (ratio * ratio) * 0.25))

    def _days_balance_score(self, estado, d) -> float:
        """Premia empleados con menos días trabajados.
        0 días → 1.0, 5 días → 0.0"""
        n_days = len(estado.dias_trabajados)
        if d in estado.dias_trabajados:
            return max(0.0, 1.0 - n_days * 0.15)  # Ya trabaja hoy, bonus menor
        return max(0.0, 1.0 - n_days * 0.2)

    def _quality_factor(self, ws_id: str) -> float:
        qmap = self.modelo.obs_global.get("quality_ws_avg", {}) or {}
        score = qmap.get(ws_id)
        if score is None:
            return 0.0
        try:
            return max(-0.10, min(0.10, (float(score) - 70.0) / 200.0))
        except Exception:
            return 0.0

    def _suggestion_penalty(self, ws_id: str) -> float:
        prob = (self.modelo.obs_global.get("ws_problematicas_sugerencias", {}) or {}).get(ws_id, 0)
        return min(0.05, float(prob) * 0.003)

    def _violation_penalty(self, ws_id: str) -> float:
        prob = (self.modelo.obs_global.get("ws_violation_penalty", {}) or {}).get(ws_id, 0)
        return min(0.05, float(prob) * 0.005)

    def _hybrid_bonus(self, ws_a: str, ws_b: str) -> float:
        pair_key = "|".join(sorted([ws_a, ws_b]))
        freq = (self.modelo.obs_global.get("hybrid_pair_freq", {}) or {}).get(pair_key, 0)
        return min(0.15, float(freq) * 0.02)

    def _daily_hours_score(self, estado, d, max_horas_dia) -> float:
        """
        Penaliza empleados que ya tienen muchas horas HOY.
        Esto fuerza distribución: si Empleado A ya tiene 4h hoy,
        prefiere Empleado B que tiene 0h hoy.

        0h hoy → 1.0 (máxima prioridad)
        3h hoy → 0.7
        5h hoy → 0.4
        7h+ hoy → 0.1
        """
        hoy_min = 0
        for dd, ws, s, e in estado.asignaciones:
            if dd == d:
                hoy_min += e - s
        hoy_h = hoy_min / 60.0
        max_h = max(1, max_horas_dia)
        ratio = hoy_h / max_h  # 0.0 = sin horas, 1.0 = al máximo
        # Curva: cae rápido después de la mitad del máximo
        return max(0.05, 1.0 - (ratio * 1.1))

    def score(self, emp, dm, d, estado, n_emps, prom_min_sem):
        emp_id, ws_id, dow = str(emp.id), str(dm.wsid), d.weekday()

        # 1) Afinidad histórica emp-ws (¿ha trabajado aquí antes?)
        pat = self.modelo.afinidad_emp_ws.get((emp_id, ws_id))
        if pat and pat.frecuencia > 0:
            max_f = max((p.frecuencia for k, p in self.modelo.afinidad_emp_ws.items() if k[1] == ws_id), default=1)
            s_af = min(1.0, pat.frecuencia / max(1, max_f))
        else:
            s_af = 0.05

        # 2) Horario típico (¿este horario es normal para este ws?)
        ph = self.modelo.horarios_ws.get((ws_id, dow))
        if ph and ph.frecuencia > 0:
            dist = (abs(_t2m(dm.start) - ph.inicio_tipico_min) + abs(_end_min(dm.end) - ph.fin_tipico_min)) / 2.0
            s_h = max(0.0, 1.0 - dist / 480.0)
        else:
            s_h = 0.5

        # 3) BALANCE DE CARGA SEMANAL
        s_balance = self._balance_score(estado, prom_min_sem)

        # 4) Balance de días trabajados
        s_days = self._days_balance_score(estado, d)

        # 5) Déficit semanal (horas restantes vs contratadas)
        s_def = self._weekly_deficit_score(emp, estado)

        # 6) BALANCE DIARIO — penaliza empleados con muchas horas HOY
        max_hdia = getattr(self, "_max_horas_dia", 10)
        s_daily = self._daily_hours_score(estado, d, max_hdia)

        # 7) Continuidad (bonus REDUCIDO si ya trabaja hoy en el mismo ws)
        # Antes era 0.8/0.4/0.2 — ahora 0.5/0.2/0.1 para no dominar
        tiene_hoy = d in estado.dias_trabajados
        mismo_ws = any(ws == ws_id for dd, ws, _, _ in estado.asignaciones if dd == d)
        s_cont = 0.5 if mismo_ws else (0.2 if tiene_hoy else 0.1)

        # 8) Día frecuente
        s_dia = 0.3
        if pat and dow in pat.dias_frecuentes:
            idx = pat.dias_frecuentes.index(dow)
            s_dia = max(0.3, 1.0 - idx * 0.15)

        bonus_q = self._quality_factor(ws_id)
        penalty_s = self._suggestion_penalty(ws_id)
        penalty_v = self._violation_penalty(ws_id)

        # ══ PESOS: BALANCE SEMANAL + DIARIO dominan (50%) ══
        score = (
            0.08 * s_af  # Afinidad histórica
            + 0.04 * s_h  # Horario típico
            + 0.22 * s_balance  # BALANCE DE CARGA SEMANAL
            + 0.08 * s_days  # Balance de días
            + 0.20 * s_def  # Déficit semanal
            + 0.22 * s_daily  # BALANCE DIARIO (NUEVO - evita saturar 1 persona/día)
            + 0.04 * s_cont  # Continuidad (reducido)
            + 0.04 * s_dia  # Día frecuente
            + bonus_q
            - penalty_s
            - penalty_v
        )
        # Bonus extra para empleados SIN asignación (forzar distribución)
        if estado.minutos_semana == 0:
            score += 0.15

        # ── AJUSTES POR SUGERENCIAS PREVIAS ──
        hints = getattr(self, "suggestion_hints", {})
        emp_name = self._emp_name_map.get(emp_id, "").upper()
        if hints and emp_name:
            if emp_name in hints.get("emps_sin_asignacion", set()):
                score += 0.20
            if emp_name in hints.get("emps_subutilizados", set()):
                score += 0.10
            if emp_name in hints.get("emps_sobrecargados", set()):
                score -= 0.15
            ws_name = getattr(dm, "wsname", "") or ""
            ws_gaps = hints.get("ws_con_gaps", {}).get(ws_name.strip().upper(), 0)
            if ws_gaps > 0:
                score += min(0.10, ws_gaps * 0.01)

        return round(max(0.0, min(1.5, score)), 4)

    def score_hybrid(self, emp, grp, d, estado, n_emps, prom_min_sem):
        dm_a = type("Tmp", (), {"wsid": grp.wsid_a, "start": grp.start, "end": grp.end})()
        dm_b = type("Tmp", (), {"wsid": grp.wsid_b, "start": grp.start, "end": grp.end})()
        s1 = self.score(emp, dm_a, d, estado, n_emps, prom_min_sem)
        s2 = self.score(emp, dm_b, d, estado, n_emps, prom_min_sem)
        bonus_h = self._hybrid_bonus(str(grp.wsid_a), str(grp.wsid_b))
        s_def = self._weekly_deficit_score(emp, estado)
        return round(min(s1, s2) * 0.55 + ((s1 + s2) / 2.0) * 0.20 + bonus_h + 0.05 + (0.20 * s_def), 4)


# ═══════════════════════════════════════════════════════════════════
# GENERADOR PRINCIPAL
# ═══════════════════════════════════════════════════════════════════


class AIScheduleGenerator:
    def __init__(self, modelo: ModeloPatrones, reglas=None, debug: bool = True):
        self.modelo = modelo or ModeloPatrones()
        self.validador = ValidadorReglasDuras(reglas)
        self.scorer = ScorerCandidatos(self.modelo)
        self.debug = debug
        self.reglas = reglas or dict(REGLAS_DURAS_DEFAULTS)

    def _log(self, msg: str):
        if self.debug:
            print(f"[AI-GEN] {msg}")

    def _coverage_pct_from_cov(self, coverage_stats) -> float:
        total_req = sum(cs["demand"].need for cs in coverage_stats.values())
        total_cov = sum(cs["covered"] for cs in coverage_stats.values())
        return round((total_cov / total_req) * 100.0, 1) if total_req else 100.0

    def generar(self, emps, demands, week, overrides=None, hybrid_groups=None, min_coverage_pct: float = 80.0):
        overrides = overrides or set()
        hybrid_groups = hybrid_groups or []
        self._log(
            f"Generando: {len(emps)} emps, {len(demands)} demands, {len(hybrid_groups)} hybrid_groups, "
            f"{week[0]}→{week[-1]}, {len(overrides)} overrides"
        )

        estados = {str(e.id): EstadoEmpleado(emp_id=str(e.id)) for e in emps}
        sched = defaultdict(list)
        coverage_stats = {}
        remaining = {}

        for dm in demands:
            coverage_stats[dm.id] = {
                "demand": dm,
                "met": 0,
                "covered": 0,
                "unmet": dm.need,
                "coverage_pct": 0.0,
                "employees": [],
            }
            remaining[dm.id] = dm.need

        total_demand_min = sum(_seg_min(dm.start, dm.end) * dm.need for dm in demands)
        active_emps = [e for e in emps if not all(e.off(d) or e.absent_day(d) for d in week)]
        prom_min = total_demand_min / max(1, len(active_emps))
        self._log(f"Promedio objetivo: {prom_min/60:.1f}h/sem, {len(active_emps)} activos")

        hyb_filled = self._fase_hibridos(
            emps, hybrid_groups, sched, estados, coverage_stats, remaining, overrides, prom_min
        )
        if hyb_filled:
            self._log(f"[FASE HYB] grupos asignados={hyb_filled}")

        demand_pri = []
        for dm in demands:
            if dm.wsid is None:
                continue
            n_cand = sum(1 for e in emps if e.can(dm.wsid) and not e.off(dm.date) and not e.absent_day(dm.date))
            is_night = _t2m(dm.start) >= 20 * 60
            is_wknd = dm.date.weekday() >= 5
            prio = (
                n_cand * 10
                - (50 if is_night else 0)
                - (30 if is_wknd else 0)
                - (20 if getattr(dm, "has_hybrid_component", False) else 0)
            )
            demand_pri.append((prio, dm))
        demand_pri.sort(key=lambda x: (x[0], x[1].date, _t2m(x[1].start)))

        assigned = 0
        for _, dm in demand_pri:
            if dm.wsid is None:
                continue
            if remaining.get(dm.id, 0) <= 0:
                continue
            for _ in range(remaining.get(dm.id, 0)):
                best = self._mejor_candidato(emps, dm, estados, overrides, prom_min)
                if best:
                    self._asignar(best, dm, sched, estados, coverage_stats, remaining)
                    assigned += 1
                else:
                    break
        self._log(f"[FASE 1] Asignados: {assigned}")

        self._pase_extra(emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 1.5, "FASE 2")
        self._pase_extra(emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 2.5, "FASE 3")

        removed, _rec, _rb, _pv = self._filtrar_bloques_cortos(
            sched,
            estados,
            coverage_stats,
            remaining,
            emps=emps,
            demands=demands,
            overrides=overrides,
        )
        self._pase_extra(
            emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 2.0, "POST-FILTER"
        )
        self._fase_hibridos(emps, hybrid_groups, sched, estados, coverage_stats, remaining, overrides, prom_min)

        # ── LOOP DE COBERTURA CON RELAJACIÓN PROGRESIVA DE REGLAS BLANDAS ──
        # Según PDF sección 4.2, orden de ruptura preferente:
        #   1) Eliminar un día de descanso (+1 día trabajo)
        #   2) Asignar más horas diarias (max_horas_dia +1, +2)
        #   3) Aceptar bloques más cortos (min 2h en vez de 3h)
        # Cada paso solo se activa si la cobertura sigue bajo el piso.
        # Las reglas DURAS (solapamiento, disponibilidad, skills) NUNCA se relajan.
        coverage = self._coverage_pct_from_cov(coverage_stats)

        # Paso 0: pases normales con multiplicador de carga
        floor_passes = 0
        multipliers = [3.0, 4.0, 5.0, 8.0]
        while coverage < min_coverage_pct and floor_passes < len(multipliers):
            mult = multipliers[floor_passes]
            self._log(f"[FLOOR-{floor_passes+1}] cobertura {coverage}% < {min_coverage_pct}% → mult={mult}")
            filled = self._pase_extra(
                emps,
                demands,
                sched,
                estados,
                coverage_stats,
                remaining,
                overrides,
                prom_min * mult,
                f"FLOOR-{floor_passes+1}",
            )
            self._fase_hibridos(emps, hybrid_groups, sched, estados, coverage_stats, remaining, overrides, prom_min)
            new_cov = self._coverage_pct_from_cov(coverage_stats)
            if new_cov <= coverage and filled == 0:
                break
            coverage = new_cov
            floor_passes += 1

        # Paso 1: Relajar +1 día de trabajo (regla blanda #1 del PDF)
        if coverage < min_coverage_pct:
            self._log(f"[RELAX-1] cobertura {coverage}% → relajando max_dias +1")
            orig_max_dias = self.validador.reglas.get("max_dias_trabajo_semana", 5)
            self.validador.reglas["max_dias_trabajo_semana"] = orig_max_dias + 1
            filled = self._pase_extra(
                emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 5.0, "RELAX-DIAS"
            )
            self._fase_hibridos(emps, hybrid_groups, sched, estados, coverage_stats, remaining, overrides, prom_min)
            self.validador.reglas["max_dias_trabajo_semana"] = orig_max_dias
            coverage = self._coverage_pct_from_cov(coverage_stats)
            if filled:
                self._log(f"[RELAX-1] +{filled} slots → cobertura {coverage}%")

        # Paso 2: Relajar max_horas_dia +1h (regla blanda #2 del PDF)
        if coverage < min_coverage_pct:
            self._log(f"[RELAX-2] cobertura {coverage}% → relajando max_horas_dia +1h")
            orig_max_horas = self.validador.reglas.get("max_horas_por_dia", 9)
            self.validador.reglas["max_horas_por_dia"] = orig_max_horas + 1
            filled = self._pase_extra(
                emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 5.0, "RELAX-HDIA"
            )
            self._fase_hibridos(emps, hybrid_groups, sched, estados, coverage_stats, remaining, overrides, prom_min)
            self.validador.reglas["max_horas_por_dia"] = orig_max_horas
            coverage = self._coverage_pct_from_cov(coverage_stats)
            if filled:
                self._log(f"[RELAX-2] +{filled} slots → cobertura {coverage}%")

        # Paso 3: Combinar +1 día Y +1h/día
        if coverage < min_coverage_pct:
            self._log(f"[RELAX-3] cobertura {coverage}% → relajando dias+1 Y horas+1")
            orig_max_dias = self.validador.reglas.get("max_dias_trabajo_semana", 5)
            orig_max_horas = self.validador.reglas.get("max_horas_por_dia", 9)
            self.validador.reglas["max_dias_trabajo_semana"] = orig_max_dias + 1
            self.validador.reglas["max_horas_por_dia"] = orig_max_horas + 1
            filled = self._pase_extra(
                emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 8.0, "RELAX-COMBO"
            )
            self._fase_hibridos(emps, hybrid_groups, sched, estados, coverage_stats, remaining, overrides, prom_min)
            self.validador.reglas["max_dias_trabajo_semana"] = orig_max_dias
            self.validador.reglas["max_horas_por_dia"] = orig_max_horas
            coverage = self._coverage_pct_from_cov(coverage_stats)
            if filled:
                self._log(f"[RELAX-3] +{filled} slots → cobertura {coverage}%")

        # Paso 4: Relajar bloques cortos (min 2h en vez de 3h)
        if coverage < min_coverage_pct:
            self._log(f"[RELAX-4] cobertura {coverage}% → relajando min_turno a 2h + dias+1 + horas+1")
            orig_min_turno = self.validador.reglas.get("min_duracion_turno_horas", 3)
            orig_max_dias = self.validador.reglas.get("max_dias_trabajo_semana", 5)
            orig_max_horas = self.validador.reglas.get("max_horas_por_dia", 9)
            self.validador.reglas["min_duracion_turno_horas"] = 2
            self.validador.reglas["max_dias_trabajo_semana"] = orig_max_dias + 1
            self.validador.reglas["max_horas_por_dia"] = orig_max_horas + 1
            filled = self._pase_extra(
                emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 10.0, "RELAX-FULL"
            )
            self._fase_hibridos(emps, hybrid_groups, sched, estados, coverage_stats, remaining, overrides, prom_min)
            self.validador.reglas["min_duracion_turno_horas"] = orig_min_turno
            self.validador.reglas["max_dias_trabajo_semana"] = orig_max_dias
            self.validador.reglas["max_horas_por_dia"] = orig_max_horas
            coverage = self._coverage_pct_from_cov(coverage_stats)
            if filled:
                self._log(f"[RELAX-4] +{filled} slots → cobertura {coverage}%")

        # ── DIAGNÓSTICO DE RECHAZOS para demands no cubiertas ──
        if coverage < min_coverage_pct:
            reject_reasons = Counter()
            unmet_demands = [dm for dm in demands if dm.wsid and remaining.get(dm.id, 0) > 0]
            sample = unmet_demands[:50]
            for dm in sample:
                for e in emps:
                    ok, reason = self.validador.puede_asignar(e, dm, dm.date, estados[str(e.id)], overrides)
                    if not ok:
                        reject_reasons[reason] += 1
            self._log(f"[DIAG] Rechazos en {len(sample)} demands unmet (top razones):")
            for reason, cnt in reject_reasons.most_common(10):
                self._log(f"  {reason}: {cnt}")

            # Diagnóstico por workstation: qué puestos quedan descubiertos y cuántos emps los cubren
            ws_unmet = Counter()
            ws_names = {}
            for dm in unmet_demands:
                ws_unmet[str(dm.wsid)] += remaining.get(dm.id, 0)
                ws_names[str(dm.wsid)] = getattr(dm, "wsname", str(dm.wsid))
            self._log(f"[DIAG-WS] Workstations con demands unmet ({len(ws_unmet)}):")
            for wsid, unmet_cnt in ws_unmet.most_common(15):
                n_emps_with_skill = sum(
                    1
                    for e in emps
                    if e.can(
                        wsid
                        if not isinstance(wsid, str)
                        else next((dm.wsid for dm in demands if str(dm.wsid) == wsid), None)
                    )
                )
                self._log(
                    f"  {ws_names.get(wsid, wsid)[:25]:25s} unmet={unmet_cnt:3d} emps_habilitados={n_emps_with_skill:2d}"
                )

        # NOTA: NO se relajan reglas duras (max_horas_dia, etc.) para evitar
        # violaciones de solapamiento y restricciones. La cobertura se maximiza
        # solo con +1 día de trabajo (regla blanda según PDF sección 4.2).

        # ── POST-RELAX: Revertir exceso de días si es posible ──
        # RELAX-1 puede dejar empleados con +1 día extra. Si el empleado
        # excede max_dias_trabajo_semana ORIGINAL, intentamos quitar su día
        # con MENOR impacto en cobertura (preferimos quitar el día donde
        # menos demandas dependen exclusivamente de ese empleado).
        orig_max_dias = 7 - self.reglas.get("dias_descanso_semana", 2)
        excess_removed = 0
        for e in emps:
            est = estados.get(str(e.id))
            if not est or len(est.dias_trabajados) <= orig_max_dias:
                continue
            excess = len(est.dias_trabajados) - orig_max_dias
            # Calcular impacto por día: cuántas asignaciones tiene ese día
            # y cuántas de esas demandas quedarían sin cubrir
            day_impact = []
            for d_work in sorted(est.dias_trabajados):
                assigns_on_day = [
                    (emp2, dm2)
                    for emp2, dm2 in sched.get(d_work, [])
                    if str(emp2.id) == str(e.id) and dm2.wsid is not None
                ]
                # Impacto = número de demandas que SOLO este empleado cubre
                exclusive = 0
                for emp2, dm2 in assigns_on_day:
                    cs = coverage_stats.get(dm2.id, {})
                    if cs.get("covered", 0) <= 1:
                        exclusive += 1
                day_impact.append((exclusive, len(assigns_on_day), d_work))
            # Ordenar: quitar primero días con menor impacto exclusivo
            day_impact.sort(key=lambda x: (x[0], x[1]))
            for i in range(min(excess, len(day_impact))):
                _, n_assigns, d_remove = day_impact[i]
                if day_impact[i][0] > 0:
                    # Tiene asignaciones exclusivas — no quitar
                    continue
                # Quitar todas las asignaciones de ese día
                keep = []
                for emp2, dm2 in sched.get(d_remove, []):
                    if str(emp2.id) == str(e.id) and dm2.wsid is not None:
                        s, end = _t2m(dm2.start), _end_min(dm2.end)
                        est.desregistrar(d_remove, str(dm2.wsid), s, end)
                        remaining[dm2.id] = remaining.get(dm2.id, 0) + 1
                        coverage_stats[dm2.id]["covered"] = max(0, coverage_stats[dm2.id]["covered"] - 1)
                        coverage_stats[dm2.id]["met"] = max(0, coverage_stats[dm2.id]["met"] - 1)
                        coverage_stats[dm2.id]["unmet"] += 1
                        excess_removed += 1
                    else:
                        keep.append((emp2, dm2))
                sched[d_remove] = keep
        if excess_removed:
            self._log(f"[POST-RELAX] Removidos {excess_removed} slots de empleados con exceso de días")
            # Re-fill lo removido con otros empleados
            filled_back = self._pase_extra(
                emps, demands, sched, estados, coverage_stats, remaining, overrides, prom_min * 3.0, "POST-RELAX-REFILL"
            )
            if filled_back:
                self._log(f"[POST-RELAX] Re-asignados {filled_back} slots a otros empleados")

        # ── VALIDACIÓN FINAL DE BLOQUES MÍNIMOS ──────────────────────────────
        # Captura bloques cortos creados por RELAX-4 (min_turno=2h temporal) o
        # aislados por POST-RELAX. Usa el filtro corregido (por bloque, no por
        # empleado) con intento de recuperación y log detallado.
        fin_rem, _, _, _ = self._filtrar_bloques_cortos(
            sched,
            estados,
            coverage_stats,
            remaining,
            emps=emps,
            demands=demands,
            overrides=overrides,
            label="FINAL-3H",
        )
        if fin_rem:
            # Refill en modo ESTRICTO: allow_short_block_provisional=False evita
            # que _pase_extra reintroduzca el mismo bloque corto que se acaba de
            # eliminar (ciclo FINAL-3H → POST-FINAL-3H → bloque corto re-añadido).
            refill_strict = self._pase_extra(
                emps,
                demands,
                sched,
                estados,
                coverage_stats,
                remaining,
                overrides,
                prom_min * 2.0,
                "POST-FINAL-3H",
                allow_short_block_provisional=False,
            )
            removed += fin_rem

        # ── SHORT-BLOCK-RECOVERY PASS ─────────────────────────────────────────
        # Construye nuevos bloques continuos >= 3h para demandas aún no cubiertas.
        # Se ejecuta ANTES de FINAL-3H-CHECK para que éste actúe de red de
        # seguridad adicional sobre cualquier error en la fase de recuperación.
        sbr_c, sbr_a, sbr_s, sbr_b, sbr_r = self._short_block_recovery_pass(
            emps,
            demands,
            sched,
            estados,
            coverage_stats,
            remaining,
            overrides,
        )
        self._log(
            f"[SHORT-BLOCK-RECOVERY] candidates={sbr_c} | applied={sbr_a} | "
            f"slots_added={sbr_s} | blocks_created={sbr_b} | "
            f"rejected_under_3h={sbr_r}"
        )

        # ── VERIFICACIÓN DE SEGURIDAD FINAL ─────────────────────────────────
        # Confirma que ningún bloque continuo < 3h permanece en el horario final
        # (p.ej. por bloques que FINAL-3H no eliminó porque estaban en split-shifts
        # conservados, y POST-FINAL-3H agregó algo adyacente pero aún corto).
        safety_rem, _, _, _ = self._filtrar_bloques_cortos(
            sched,
            estados,
            coverage_stats,
            remaining,
            label="FINAL-3H-CHECK",
        )
        refill_strict = refill_strict if fin_rem else 0
        self._log(f"[FINAL-3H-STRICT] refill_slots={refill_strict} | " f"final_short_blocks={safety_rem}")
        if safety_rem:
            removed += safety_rem

        # ── SCHEDULE GAP FILLING PASS ────────────────────────────────────────
        # Rellena huecos operativos extendiendo bloques existentes (EXTEND),
        # creando segundos turnos partidos válidos (SPLIT) o nuevos bloques
        # desde cero para empleados libres/subutilizados (NEW).
        # El histórico se usa SOLO para ranking; las reglas no se relajan.
        gfp = self._gap_filling_pass(
            emps,
            demands,
            sched,
            estados,
            coverage_stats,
            remaining,
            overrides,
            self.modelo,
        )
        # Guardar resultado para que agenda.py pueda exponerlo sin alterar lógica
        self._last_gfp_result = gfp
        # Red de seguridad post-filler: eliminar cualquier bloque corto residual
        gfp_check_rem, _, _, _ = self._filtrar_bloques_cortos(
            sched,
            estados,
            coverage_stats,
            remaining,
            label="GAP-FILLER-CHECK",
        )
        if gfp_check_rem:
            removed += gfp_check_rem

        for cs in coverage_stats.values():
            n = cs["demand"].need
            cs["coverage_pct"] = round((cs["covered"] / n) * 100, 1) if n > 0 else 100.0

        diag = self._diag_descanso(emps, week, estados)
        total_req = sum(dm.need for dm in demands)
        total_cov = sum(cs["covered"] for cs in coverage_stats.values())
        pct = round(total_cov / total_req * 100, 1) if total_req else 100.0
        self._log(f"══ RESULTADO: {total_cov}/{total_req} = {pct}% ══")
        self._log(f"   Removidos por 3h/bloque: {removed}")

        # ── DIAGNÓSTICO DE EQUIDAD ──
        hours_list = []
        sin_asig = 0
        for e in emps:
            est = estados.get(str(e.id))
            h = est.minutos_semana / 60.0 if est else 0
            hours_list.append(h)
            if h == 0 and not all(e.off(d) or e.absent_day(d) for d in week):
                sin_asig += 1
        if hours_list:
            avg_h = sum(hours_list) / len(hours_list)
            working = [h for h in hours_list if h > 0]
            avg_working = sum(working) / len(working) if working else 0
            max_h = max(hours_list)
            min_working = min(working) if working else 0
            over_130 = sum(1 for h in working if h > avg_working * 1.3)
            under_70 = sum(1 for h in working if h < avg_working * 0.7)
            self._log(f"[EQUIDAD] Promedio general: {avg_h:.1f}h | Promedio trabajando: {avg_working:.1f}h")
            self._log(f"[EQUIDAD] Max: {max_h:.1f}h | Min(trab): {min_working:.1f}h | Sin asig: {sin_asig}")
            self._log(f"[EQUIDAD] >130% promedio: {over_130} | <70% promedio: {under_70}")

        return sched, coverage_stats, diag

    def _mejor_candidato(self, emps, dm, estados, overrides, prom_min, allow_short_block_provisional: bool = True):
        best_emp, best_sc = None, -1.0
        for e in emps:
            ok, _ = self.validador.puede_asignar(
                e,
                dm,
                dm.date,
                estados[str(e.id)],
                overrides,
                allow_short_block_provisional=allow_short_block_provisional,
            )
            if not ok:
                continue
            sc = self.scorer.score(e, dm, dm.date, estados[str(e.id)], len(emps), prom_min)
            if sc > best_sc:
                best_sc, best_emp = sc, e
        return best_emp

    def _mejor_candidato_hibrido(self, emps, grp, estados, overrides, prom_min):
        best_emp, best_sc = None, -1.0
        for e in emps:
            ok, _ = self.validador.puede_asignar_hibrido(e, grp, grp.date, estados[str(e.id)], overrides)
            if not ok:
                continue
            sc = self.scorer.score_hybrid(e, grp, grp.date, estados[str(e.id)], len(emps), prom_min)
            if sc > best_sc:
                best_sc, best_emp = sc, e
        return best_emp

    def _asignar(self, emp, dm, sched, estados, cov, remaining):
        sched[dm.date].append((emp, dm))
        s, e = _t2m(dm.start), _end_min(dm.end)
        estados[str(emp.id)].registrar(dm.date, str(dm.wsid), s, e)
        remaining[dm.id] = max(0, remaining.get(dm.id, 0) - 1)
        cov[dm.id]["met"] += 1
        cov[dm.id]["covered"] += 1
        cov[dm.id]["unmet"] = max(0, cov[dm.id]["unmet"] - 1)
        cov[dm.id]["employees"].append(str(emp.id))

    def _asignar_hibrido(self, emp, grp, sched, estados, cov, remaining):
        for dm in getattr(grp, "demands", []):
            dm.observation_override = "BT"
            if str(dm.wsid) == str(grp.wsid_a):
                dm.hybrid_partner_wsid = grp.wsid_b
            elif str(dm.wsid) == str(grp.wsid_b):
                dm.hybrid_partner_wsid = grp.wsid_a
            dm.hybrid_group_id = grp.id
            sched[grp.date].append((emp, dm))

        estados[str(emp.id)].registrar(
            grp.date,
            f"HYB:{grp.wsid_a}|{grp.wsid_b}",
            _t2m(grp.start),
            _end_min(grp.end),
        )

        for dm in getattr(grp, "demands", []):
            remaining[dm.id] = max(0, remaining.get(dm.id, 0) - 1)
            cov[dm.id]["met"] += 1
            cov[dm.id]["covered"] += 1
            cov[dm.id]["unmet"] = max(0, cov[dm.id]["unmet"] - 1)
            cov[dm.id]["employees"].append(str(emp.id))

    def _fase_hibridos(self, emps, hybrid_groups, sched, estados, cov, remaining, overrides, prom_min):
        filled = 0
        for grp in sorted(hybrid_groups, key=lambda g: (g.date, _t2m(g.start), str(g.wsid_a), str(g.wsid_b))):
            if all(remaining.get(dm.id, 0) <= 0 for dm in getattr(grp, "demands", [])):
                continue
            best = self._mejor_candidato_hibrido(emps, grp, estados, overrides, prom_min)
            if best:
                self._asignar_hibrido(best, grp, sched, estados, cov, remaining)
                filled += 1
        return filled

    def _pase_extra(
        self,
        emps,
        demands,
        sched,
        estados,
        cov,
        remaining,
        overrides,
        prom,
        label,
        allow_short_block_provisional: bool = True,
    ):
        filled = 0
        for dm in sorted(demands, key=lambda d: (d.date, _t2m(d.start), str(d.wsid))):
            if dm.wsid is None or remaining.get(dm.id, 0) <= 0:
                continue
            for _ in range(remaining[dm.id]):
                best = self._mejor_candidato(
                    emps,
                    dm,
                    estados,
                    overrides,
                    prom,
                    allow_short_block_provisional=allow_short_block_provisional,
                )
                if best:
                    self._asignar(best, dm, sched, estados, cov, remaining)
                    filled += 1
                else:
                    break
        if filled:
            self._log(f"[{label}] +{filled} slots")
        return filled

    # ── HELPERS PARA VALIDACIÓN DE BLOQUES MÍNIMOS ─────────────────────────

    def _get_contiguous_blocks_for_employee_day(self, pairs):
        """
        Agrupa las asignaciones de un empleado en un día en bloques continuos.
        Retorna lista de dicts con:
            start_min, end_min, duration_min, assignments [(emp, dm), ...]
        """
        if not pairs:
            return []
        sorted_pairs = sorted(pairs, key=lambda x: _t2m(x[1].start))
        emp0, dm0 = sorted_pairs[0]
        current = {
            "start_min": _t2m(dm0.start),
            "end_min": _end_min(dm0.end),
            "assignments": [(emp0, dm0)],
        }
        blocks: List[dict] = []
        for emp, dm in sorted_pairs[1:]:
            s = _t2m(dm.start)
            e = _end_min(dm.end)
            if s <= current["end_min"]:  # Contiguo o solapado
                current["end_min"] = max(current["end_min"], e)
                current["assignments"].append((emp, dm))
            else:
                current["duration_min"] = current["end_min"] - current["start_min"]
                blocks.append(current)
                current = {"start_min": s, "end_min": e, "assignments": [(emp, dm)]}
        current["duration_min"] = current["end_min"] - current["start_min"]
        blocks.append(current)
        return blocks

    def _recover_short_block(self, eid, d, blk, estados, cov, remaining, demands, overrides, min_blk_min):
        """
        Intenta extender un bloque corto añadiendo demandas adyacentes no cubiertas.

        Busca demandas del mismo día que:
          - Empiezan donde termina el bloque (extensión forward) o
          - Terminan donde empieza el bloque (extensión backward)
          - El empleado tiene el skill requerido
          - La asignación pasa puede_asignar() (sin violar reglas duras)

        Hace rollback completo si no puede alcanzar min_blk_min.

        Retorna:
            (added_assignments, new_blk_dur)
            added_assignments = [(emp, dm)] — nuevas asignaciones (estado/cov/remaining ya
                                              actualizados si new_blk_dur >= min_blk_min).
            Si falla, retorna ([], blk["duration_min"]) con rollback aplicado.
        """
        emp = blk["assignments"][0][0]
        estado = estados[eid]
        blk_s = blk["start_min"]
        blk_e = blk["end_min"]
        current_dur = blk_e - blk_s

        added: List[Tuple[Any, Any, int, int]] = []  # (emp, dm, s, e) para rollback
        added_assignments: List[Tuple[Any, Any]] = []  # (emp, dm) para retornar

        changed = True
        while current_dur < min_blk_min and changed:
            changed = False
            candidates = []
            for dm in demands:
                if dm.wsid is None or remaining.get(dm.id, 0) <= 0 or dm.date != d:
                    continue
                dm_s = _t2m(dm.start)
                dm_e = _end_min(dm.end)
                if dm_s == blk_e:  # Extensión forward
                    candidates.append((0, dm_s, dm))
                elif dm_e == blk_s:  # Extensión backward
                    candidates.append((1, -dm_e, dm))

            candidates.sort(key=lambda x: (x[0], x[1]))

            for _, _, dm in candidates:
                if remaining.get(dm.id, 0) <= 0:
                    continue
                ok, _ = self.validador.puede_asignar(emp, dm, d, estado, overrides)
                if not ok:
                    continue

                dm_s = _t2m(dm.start)
                dm_e = _end_min(dm.end)
                estado.registrar(d, str(dm.wsid), dm_s, dm_e)
                remaining[dm.id] = max(0, remaining.get(dm.id, 0) - 1)
                cov[dm.id]["covered"] = cov[dm.id].get("covered", 0) + 1
                cov[dm.id]["met"] = cov[dm.id].get("met", 0) + 1
                cov[dm.id]["unmet"] = max(0, cov[dm.id].get("unmet", 0) - 1)
                cov[dm.id].setdefault("employees", [])
                if str(emp.id) not in cov[dm.id]["employees"]:
                    cov[dm.id]["employees"].append(str(emp.id))

                added.append((emp, dm, dm_s, dm_e))
                added_assignments.append((emp, dm))

                blk_s = min(blk_s, dm_s)
                blk_e = max(blk_e, dm_e)
                current_dur = blk_e - blk_s
                changed = True
                break  # Re-evaluar candidatos con el estado actualizado

        if current_dur >= min_blk_min:
            n_added = len(added_assignments)
            if n_added > 0:
                self._log(
                    f"[3H-RECOVERY] {emp.name} {d} "
                    f"{blk_s//60:02d}:{blk_s%60:02d}-{blk_e//60:02d}:{blk_e%60:02d} "
                    f"={current_dur/60:.1f}h recuperado (+{n_added} demanda(s))"
                )
            return added_assignments, current_dur

        # Rollback
        for _, dm_r, s_r, e_r in reversed(added):
            estado.desregistrar(d, str(dm_r.wsid), s_r, e_r)
            remaining[dm_r.id] = remaining.get(dm_r.id, 0) + 1
            cov[dm_r.id]["covered"] = max(0, cov[dm_r.id]["covered"] - 1)
            cov[dm_r.id]["met"] = max(0, cov[dm_r.id]["met"] - 1)
            cov[dm_r.id]["unmet"] += 1
        return [], blk["duration_min"]

    def _filtrar_bloques_cortos(
        self, sched, estados, cov, remaining, emps=None, demands=None, overrides=None, label="3H-FILTER"
    ):
        """
        Elimina bloques continuos del empleado que sean < min_duracion_turno_horas.

        Mejoras respecto a la versión original:
          - Elimina por BLOQUE específico, no por empleado completo.
            → Un split shift con bloque corto + bloque largo conserva el largo.
          - Intenta recuperar bloques cortos añadiendo demandas adyacentes (si se
            pasan emps/demands/overrides).
          - Loguea métricas detalladas: [<label>] y [3H-RECOVERY].

        Retorna:
            (removed_slots, recovered, removed_blocks, preserved_valid_blocks)
        """
        min_blk_min = self.reglas.get("min_duracion_turno_horas", 3) * 60

        short_blocks_detected = 0
        recovered = 0
        removed_blocks = 0
        removed_slots = 0
        preserved_valid_blocks = 0
        recovery_attempts = 0
        recovery_applied = 0
        recovery_slots_added = 0

        for d in list(sched.keys()):
            # Separar AUSENCIAS (wsid=None) de asignaciones reales
            ausencias = [(emp, dm) for emp, dm in sched[d] if dm.wsid is None]
            by_emp: Dict[str, List] = defaultdict(list)
            for emp, dm in sched[d]:
                if dm.wsid is not None:
                    by_emp[str(emp.id)].append((emp, dm))

            # Construir nueva lista del día: ausencias + asignaciones validadas
            new_day = list(ausencias)

            for eid, pairs in by_emp.items():
                blocks = self._get_contiguous_blocks_for_employee_day(pairs)
                keep_for_emp: List[Tuple] = []

                for blk in blocks:
                    if blk["duration_min"] >= min_blk_min:
                        keep_for_emp.extend(blk["assignments"])
                        preserved_valid_blocks += 1
                        continue

                    # Bloque corto detectado
                    short_blocks_detected += 1
                    blk_s = blk["start_min"]
                    blk_e = blk["end_min"]
                    blk_dur = blk["duration_min"]

                    # Intentar recuperación
                    added_assignments: List[Tuple] = []
                    new_blk_dur = blk_dur
                    if emps is not None and demands is not None:
                        recovery_attempts += 1
                        added_assignments, new_blk_dur = self._recover_short_block(
                            eid,
                            d,
                            blk,
                            estados,
                            cov,
                            remaining,
                            demands,
                            overrides or set(),
                            min_blk_min,
                        )
                        if new_blk_dur >= min_blk_min:
                            recovery_applied += 1
                            recovery_slots_added += len(added_assignments)

                    if new_blk_dur >= min_blk_min:
                        # Recuperado: conservar originales + nuevos
                        recovered += 1
                        keep_for_emp.extend(blk["assignments"])
                        keep_for_emp.extend(added_assignments)
                    else:
                        # Eliminar solo este bloque
                        other_valid = sum(1 for b in blocks if b["duration_min"] >= min_blk_min)
                        emp_name = blk["assignments"][0][0].name if blk["assignments"] else eid
                        self._log(
                            f"[3H-BLK] {emp_name} {d} bloque "
                            f"{blk_s//60:02d}:{blk_s%60:02d}-{blk_e//60:02d}:{blk_e%60:02d} "
                            f"= {blk_dur/60:.1f}h < {min_blk_min//60}h "
                            f"→ eliminando {len(blk['assignments'])} seg."
                            + (f" | conservando {other_valid} bloque(s) válido(s)" if other_valid > 0 else "")
                        )
                        removed_blocks += 1
                        for _, dm_r in blk["assignments"]:
                            s_r, e_r = _t2m(dm_r.start), _end_min(dm_r.end)
                            estados[eid].desregistrar(d, str(dm_r.wsid), s_r, e_r)
                            remaining[dm_r.id] = remaining.get(dm_r.id, 0) + 1
                            cov[dm_r.id]["covered"] = max(0, cov[dm_r.id]["covered"] - 1)
                            cov[dm_r.id]["met"] = max(0, cov[dm_r.id]["met"] - 1)
                            cov[dm_r.id]["unmet"] += 1
                            removed_slots += 1

                new_day.extend(keep_for_emp)

            sched[d] = new_day

        if recovery_attempts > 0:
            self._log(
                f"[3H-RECOVERY] attempts={recovery_attempts} | applied={recovery_applied} | "
                f"slots_added={recovery_slots_added}"
            )
        self._log(
            f"[{label}] short_blocks_detected={short_blocks_detected} | recovered={recovered} | "
            f"removed_blocks={removed_blocks} | removed_slots={removed_slots} | "
            f"preserved_valid_blocks={preserved_valid_blocks}"
        )
        return removed_slots, recovered, removed_blocks, preserved_valid_blocks

    # ── SHORT-BLOCK-RECOVERY PASS ─────────────────────────────────────────────

    def _validate_chain_for_employee(
        self,
        emp,
        chain: List,
        d: date,
        estado: EstadoEmpleado,
        overrides,
        min_blk_min: int,
    ) -> Tuple[bool, str]:
        """
        Valida que un empleado puede cubrir TODAS las demandas de una cadena
        simulando el efecto acumulado (no demanda a demanda).

        Comprueba:
          - skill/ventana/UserShift para cada demanda
          - max_horas_dia / max_horas_semanales
          - Solapamiento con intervalos existentes
          - max_bloques_por_dia tras merge
          - TODOS los bloques resultantes >= min_blk_min
          - min_gap_split entre bloques (si hay más de uno)
          - min_descanso_entre_turnos con días adyacentes
        """
        if emp.off(d) or emp.absent_day(d):
            return False, "DIA_LIBRE"

        max_dias = self.validador.reglas.get("max_dias_trabajo_semana", 5)
        if d not in estado.dias_trabajados and len(estado.dias_trabajados) >= max_dias:
            return False, "MAX_DIAS"

        chain_dur_total = 0
        for dm in chain:
            if not emp.can(dm.wsid):
                return False, "SIN_SKILL"
            if not emp.available(d, dm.start, dm.end):
                return False, "FUERA_VENTANA"
            if not self.validador._usershift_ok(emp, d, dm.start, dm.end, overrides):
                return False, "FUERA_USERSHIFT_WINDOW"
            dur = _seg_min(dm.start, dm.end)
            if dur <= 0:
                return False, "RANGO_INVALIDO"
            chain_dur_total += dur

        max_h_min = self.validador.reglas.get("max_horas_por_dia", 9) * 60
        if estado.minutos_por_dia.get(d, 0) + chain_dur_total > max_h_min:
            return False, "MAX_HORAS_DIA"

        if not self.validador._weekly_hours_ok(emp, estado, chain_dur_total):
            return False, "MAX_HORAS_SEMANALES"

        existing_ivs = list(estado.intervalos_por_dia.get(d, []))
        chain_ivs = [(_t2m(dm.start), _end_min(dm.end)) for dm in chain]

        for s_c, e_c in chain_ivs:
            if _has_overlap(existing_ivs, s_c, e_c):
                return False, "SOLAPAMIENTO"

        merged = _merge_intervals(existing_ivs + chain_ivs)

        max_bloques = self.validador.reglas.get("max_bloques_por_dia", 2)
        if len(merged) > max_bloques:
            return False, "MAX_BLOQUES"

        min_turno = self.validador.reglas.get("min_duracion_turno_horas", 3) * 60
        for bs, be in merged:
            if (be - bs) < min_turno:
                return False, "BLOQUE_CORTO_FINAL"

        min_gap_split = self.validador.reglas.get("min_gap_split_horas", 3) * 60
        for i in range(len(merged) - 1):
            if (merged[i + 1][0] - merged[i][1]) < min_gap_split:
                return False, "GAP_SPLIT_INSUFICIENTE"

        min_desc_min = self.validador.reglas.get("min_descanso_entre_turnos_horas", 9) * 60
        first_today = merged[0][0]
        last_today = merged[-1][1]

        d_prev = d - timedelta(days=1)
        if estado.intervalos_por_dia.get(d_prev):
            last_prev = max(e for _, e in estado.intervalos_por_dia[d_prev])
            if (1440 - last_prev) + first_today < min_desc_min:
                return False, "DESC_ENTRE_TURNOS"

        d_next = d + timedelta(days=1)
        if estado.intervalos_por_dia.get(d_next):
            first_next = min(s for s, _ in estado.intervalos_por_dia[d_next])
            if (1440 - last_today) + first_next < min_desc_min:
                return False, "DESC_ENTRE_TURNOS"

        return True, ""

    def _build_chains_for_employee_day(
        self,
        emp,
        estado: EstadoEmpleado,
        d: date,
        eligible_demands: List,
        min_blk_min: int,
    ) -> List[Tuple[List, int, float]]:
        """
        Construye todas las cadenas de demandas CONTIGUAS elegibles para un
        empleado en un día, filtrando a las que forman un bloque >= min_blk_min.

        «Contigua» significa que demand[k].end == demand[k+1].start (sin gaps).

        Retorna lista de (chain, chain_duration_min, priority_score) ordenada
        por score descendente.
        """
        if not eligible_demands:
            return []

        sorted_dms = sorted(eligible_demands, key=lambda dm: (_t2m(dm.start), str(dm.wsid)))
        existing_ivs = sorted(estado.intervalos_por_dia.get(d, []))
        max_bloques = self.validador.reglas.get("max_bloques_por_dia", 2)
        is_new_day = d not in estado.dias_trabajados

        results: List[Tuple[List, int, float]] = []
        n = len(sorted_dms)

        for i in range(n):
            # Construir la cadena maximal contigua a partir de sorted_dms[i]
            chain: List = [sorted_dms[i]]
            chain_end = _end_min(sorted_dms[i].end)
            j = i + 1
            while j < n:
                dm_next = sorted_dms[j]
                if _t2m(dm_next.start) == chain_end:
                    chain.append(dm_next)
                    chain_end = _end_min(dm_next.end)
                    j += 1
                else:
                    break

            chain_start = _t2m(chain[0].start)
            chain_dur = chain_end - chain_start

            # Verificar si el bloque resultante (merge con existentes) es >= min_blk_min
            merged = _merge_intervals(existing_ivs + [(chain_start, chain_end)])
            if len(merged) > max_bloques:
                continue

            # Bloque que contiene la cadena
            block_dur = next(
                (be - bs for bs, be in merged if bs <= chain_start and chain_end <= be),
                0,
            )
            if block_dur < min_blk_min:
                continue

            # Todos los bloques deben ser >= min_blk_min
            if any((be - bs) < min_blk_min for bs, be in merged):
                continue

            score = len(chain) * 100.0 + (50.0 if is_new_day else 0.0) + block_dur * 0.1 - estado.minutos_semana * 0.001
            results.append((chain, chain_dur, score))

        return sorted(results, key=lambda x: -x[2])

    def _short_block_recovery_pass(
        self,
        emps,
        demands,
        sched,
        estados,
        cov,
        remaining,
        overrides,
    ) -> Tuple[int, int, int, int, int]:
        """
        ShortBlockRecoveryPass: aumenta cobertura válida construyendo bloques
        continuos >= min_duracion_turno_horas para demandas no cubiertas.

        Estrategia:
          1. Agrupar demandas no cubiertas por día.
          2. Para cada día, filtrar empleados elegibles (sin día libre, dentro de
             límites) y construir cadenas de demandas CONTIGUAS que, en conjunto,
             formen un bloque >= 3h respetando los intervalos ya asignados.
          3. Rankear candidatos: mayor cobertura > empleado sin asignación hoy >
             menor carga acumulada.
          4. Aplicar cadenas atómicamente (todas las demandas o ninguna).
             Rollback completo si un segmento falla tras la validación.

        Garantía: ningún bloque < 3h queda en el horario tras este pase.
        FINAL-3H-CHECK actúa de red de seguridad adicional.

        Retorna: (candidates, applied_chains, slots_added, blocks_created, rejected_under_3h)
        """
        min_blk_min = self.reglas.get("min_duracion_turno_horas", 3) * 60

        unmet_by_day: Dict[date, List] = defaultdict(list)
        for dm in demands:
            if dm.wsid is not None and remaining.get(dm.id, 0) > 0:
                unmet_by_day[dm.date].append(dm)

        if not unmet_by_day:
            return 0, 0, 0, 0, 0

        candidates = 0
        applied_chains = 0
        slots_added = 0
        blocks_created = 0
        rejected_under_3h = 0

        for d in sorted(unmet_by_day.keys()):
            all_day_unmet = unmet_by_day[d]

            # Priorizar empleados sin asignación ese día (construyen bloques nuevos)
            emp_priority = sorted(
                emps,
                key=lambda e: (
                    1 if d in estados[str(e.id)].dias_trabajados else 0,
                    estados[str(e.id)].minutos_semana,
                ),
            )

            committed: Set[str] = set()  # demandas ya comprometidas este día
            day_candidates: List[Tuple[float, Any, List, int, str]] = []

            for emp in emp_priority:
                eid = str(emp.id)
                estado = estados[eid]

                if emp.off(d) or emp.absent_day(d):
                    continue
                max_dias = self.validador.reglas.get("max_dias_trabajo_semana", 5)
                if d not in estado.dias_trabajados and len(estado.dias_trabajados) >= max_dias:
                    continue

                eligible = [
                    dm
                    for dm in all_day_unmet
                    if emp.can(dm.wsid)
                    and emp.available(d, dm.start, dm.end)
                    and self.validador._usershift_ok(emp, d, dm.start, dm.end, overrides)
                ]
                if not eligible:
                    continue

                chains = self._build_chains_for_employee_day(
                    emp,
                    estado,
                    d,
                    eligible,
                    min_blk_min,
                )
                for chain, chain_dur, score in chains:
                    day_candidates.append((score, emp, chain, chain_dur, eid))

            # Ordenar por score descendente para aplicar primero la mejor cadena
            day_candidates.sort(key=lambda x: -x[0])

            for score, emp, chain, chain_dur, eid in day_candidates:
                candidates += 1

                if any(dm.id in committed for dm in chain):
                    continue
                if any(remaining.get(dm.id, 0) <= 0 for dm in chain):
                    continue
                if chain_dur < min_blk_min:
                    rejected_under_3h += 1
                    continue

                # Validación completa (usa estado actualizado tras cadenas previas)
                ok, _ = self._validate_chain_for_employee(
                    emp,
                    chain,
                    d,
                    estados[eid],
                    overrides,
                    min_blk_min,
                )
                if not ok:
                    continue

                # Aplicar atómicamente con rollback de seguridad
                applied: List[Tuple[Any, Any, int, int]] = []
                rollback = False
                for dm in chain:
                    try:
                        self._asignar(emp, dm, sched, estados, cov, remaining)
                        applied.append((emp, dm, _t2m(dm.start), _end_min(dm.end)))
                    except Exception:
                        rollback = True
                        break

                if rollback:
                    for emp_r, dm_r, s_r, e_r in reversed(applied):
                        estados[str(emp_r.id)].desregistrar(d, str(dm_r.wsid), s_r, e_r)
                        remaining[dm_r.id] = remaining.get(dm_r.id, 0) + 1
                        cov[dm_r.id]["covered"] = max(0, cov[dm_r.id]["covered"] - 1)
                        cov[dm_r.id]["met"] = max(0, cov[dm_r.id]["met"] - 1)
                        cov[dm_r.id]["unmet"] += 1
                        sched[d] = [
                            (e2, dm2) for e2, dm2 in sched[d] if not (str(e2.id) == str(emp_r.id) and dm2.id == dm_r.id)
                        ]
                    continue

                for dm in chain:
                    committed.add(dm.id)
                applied_chains += 1
                slots_added += len(chain)
                blocks_created += 1

        return candidates, applied_chains, slots_added, blocks_created, rejected_under_3h

    # ── DIAGNÓSTICO ───────────────────────────────────────────────────────────

    def _diag_descanso(self, emps, week, estados):
        min_off = self.reglas.get("dias_descanso_semana", 2)
        diag = []
        for e in emps:
            est = estados.get(str(e.id))
            if not est:
                continue
            dias_off = 7 - len(est.dias_trabajados)
            if dias_off < min_off:
                diag.append(
                    {
                        "employee_id": str(e.id),
                        "employee_name": e.name,
                        "days_worked": len(est.dias_trabajados),
                        "days_off": dias_off,
                        "required_off": min_off,
                    }
                )
        return diag

    # ── SCHEDULE GAP FILLING PASS ────────────────────────────────────────────

    def _score_gap_plan(
        self,
        plan: "CandidatePlan",
        estados: Dict[str, "EstadoEmpleado"],
        cov: Dict,
        modelo: Optional["ModeloPatrones"] = None,
    ) -> float:
        """
        Puntúa un CandidatePlan para ScheduleGapFillingPass.

        El histórico (modelo) se usa SOLO como bonus de ranking, nunca como
        restricción.  Los valores de reglas provienen de self.reglas.
        """
        emp = plan.emp
        eid = str(emp.id)
        estado = estados[eid]
        d = plan.d
        score = 0.0

        # ── Base: slots cubiertos ──
        score += len(plan.chain) * 100

        # ── Tipo de plan ──
        if plan.plan_type == "EXTEND":
            score += 35
        elif plan.plan_type == "SPLIT":
            score += 25
        else:  # NEW
            score += 25

        # ── Carga semanal ──
        weekly_min = estado.minutos_semana
        limit_fn = getattr(emp, "weekly_hours_limit", None)
        weekly_limit_min: Optional[int] = None
        if callable(limit_fn):
            try:
                weekly_limit_min = int(limit_fn() or 0) or None
            except Exception:
                pass

        if weekly_limit_min:
            ratio_sem = weekly_min / weekly_limit_min
            if ratio_sem < 0.5:
                score += 25  # baja carga → bonus
            projected = (weekly_min + plan.chain_dur) / weekly_limit_min
            if projected < 0.85:
                score += 20  # sin acercarse al límite
            elif projected > 0.95:
                score -= 20  # demasiado cerca del máximo semanal
        else:
            if weekly_min == 0:
                score += 25  # sin horas esta semana → máxima prioridad

        # ── Carga diaria ──
        max_h_day = self.reglas.get("max_horas_por_dia", 9) * 60
        daily_min = estado.minutos_por_dia.get(d, 0)
        projected_day = daily_min + plan.chain_dur
        if projected_day < max_h_day * 0.85:
            score += 20
        elif projected_day > max_h_day * 0.95:
            score -= 20

        # ── Solo 1 día asignado esta semana ──
        if len(estado.dias_trabajados) <= 1:
            score += 15

        # ── Sin asignación hoy ──
        if d not in estado.dias_trabajados:
            score += 15

        # ── Workstation completamente descubierta ──
        for dm in plan.chain:
            cs = cov.get(dm.id, {})
            if cs.get("covered", 0) == 0 and cs.get("unmet", 0) > 0:
                score += 10

        # ── Penalizar split innecesario ──
        if plan.plan_type == "SPLIT":
            existing_ivs = list(estado.intervalos_por_dia.get(d, []))
            if _merge_intervals(existing_ivs):
                score -= 15

        # ── HISTÓRICO — SOLO ranking, nunca filtro ──
        if modelo:
            dow = d.weekday()
            affinity_bonus = 0.0
            timing_bonus = 0.0
            for dm in plan.chain:
                ws_id = str(dm.wsid)
                pat = modelo.afinidad_emp_ws.get((eid, ws_id))
                if pat and pat.frecuencia > 0:
                    affinity_bonus += min(15.0, pat.frecuencia * 0.5)
                ph = modelo.horarios_ws.get((ws_id, dow))
                if ph and ph.frecuencia > 0:
                    dist_h = abs(_t2m(dm.start) - ph.inicio_tipico_min) / 60.0
                    if dist_h < 1.0:
                        timing_bonus += 10.0
                    elif dist_h < 2.0:
                        timing_bonus += 5.0
            # Cap: 30 puntos máximos de bonificación histórica por plan
            score += min(30.0, affinity_bonus + timing_bonus)

        return max(0.0, score)

    def _gap_filling_pass(
        self,
        emps,
        demands,
        sched,
        estados: Dict[str, "EstadoEmpleado"],
        cov: Dict,
        remaining: Dict,
        overrides,
        modelo: Optional["ModeloPatrones"] = None,
    ) -> Dict:
        """
        ScheduleGapFillingPass — rellena huecos operativos después de la
        generación base, antes del RepairEngine.

        Casos:
          EXTEND : agrega demandas contiguas al inicio/fin de un bloque válido.
          SPLIT  : crea un segundo bloque partido válido (respetando gap mínimo).
          NEW    : crea un bloque nuevo desde cero para empleado libre/subutilizado.

        Garantías:
          - Ninguna regla dura se relaja (valores desde self.reglas).
          - El histórico (modelo) se usa SOLO para ranking (bonus), nunca como filtro.
          - Aplicación atómica con rollback completo ante cualquier fallo.
          - Ningún bloque < min_duracion_turno_horas queda tras el pase.

        Retorna dict con métricas completas.
        """
        import time as _time

        t0 = _time.time()

        min_blk_min = self.reglas.get("min_duracion_turno_horas", 3) * 60
        max_bloques = self.reglas.get("max_bloques_por_dia", 2)
        max_dias = self.reglas.get("max_dias_trabajo_semana", 5)
        min_gap_split = self.reglas.get("min_gap_split_horas", 3) * 60

        gaps_before = sum(max(0, v) for v in remaining.values())
        cov_before = sum(cs["covered"] for cs in cov.values())
        reject_counts: Counter = Counter()
        plan_types_applied: Counter = Counter()
        employees_used: Set[str] = set()
        candidates_generated = 0
        candidates_applied = 0

        # ── Diagnóstico extendido ─────────────────────────────────────────────
        reject_by_ws: Dict[str, Counter] = defaultdict(Counter)
        reject_by_day: Dict[date, Counter] = defaultdict(Counter)
        ws_candidates_attempted: Dict[str, int] = defaultdict(int)
        ws_candidates_rejected: Dict[str, int] = defaultdict(int)
        emp_rejected_max_hours: Set[str] = set()
        emp_rejected_overlap: Set[str] = set()
        # Nombre legible y pool de skill por workstation (calculado una vez)
        ws_diag_name: Dict[str, str] = {}
        ws_qualified_emps: Dict[str, Set[str]] = defaultdict(set)
        for dm in demands:
            if dm.wsid is not None:
                ws_diag_name[str(dm.wsid)] = getattr(dm, "wsname", str(dm.wsid))
        for _e in emps:
            for dm in demands:
                if dm.wsid is not None and _e.can(dm.wsid):
                    ws_qualified_emps[str(dm.wsid)].add(str(_e.id))

        def _count_one_day() -> int:
            return sum(1 for e in emps if len(estados[str(e.id)].dias_trabajados) == 1)

        def _count_unassigned() -> int:
            return sum(1 for e in emps if estados[str(e.id)].minutos_semana == 0)

        one_day_before = _count_one_day()
        unassigned_before = _count_unassigned()

        # ── 1. Recoger demandas no cubiertas agrupadas por día ──
        unmet_by_day: Dict[date, List] = defaultdict(list)
        for dm in demands:
            if dm.wsid is not None and remaining.get(dm.id, 0) > 0:
                unmet_by_day[dm.date].append(dm)

        def _empty_result(elapsed_ms: int) -> Dict:
            self._log(
                f"[GAP-FILLER] candidates=0 | applied=0 | slots_added=0 | "
                f"employees_used=0 | extend_block=0 | second_split=0 | new_block=0 | "
                f"final_short_blocks=0 | time={elapsed_ms}ms"
            )
            return {
                "gaps_before": gaps_before,
                "gaps_after": gaps_before,
                "slots_added": 0,
                "employees_used": 0,
                "candidate_plans_generated": 0,
                "candidate_plans_applied": 0,
                "by_plan_type": {},
                "top_reject_reasons": {},
                "final_short_blocks": 0,
                "underutilized_employees_before": unassigned_before,
                "underutilized_employees_after": unassigned_before,
                "one_day_assigned_before": one_day_before,
                "one_day_assigned_after": one_day_before,
                "execution_time_ms": elapsed_ms,
            }

        if not unmet_by_day:
            return _empty_result(int((_time.time() - t0) * 1000))

        # ── 2. Procesar cada día ──
        for d in sorted(unmet_by_day.keys()):
            day_unmet = [dm for dm in unmet_by_day[d] if remaining.get(dm.id, 0) > 0]
            if not day_unmet:
                continue

            plans: List[CandidatePlan] = []
            committed: Set[str] = set()

            # Ordenar empleados: sin asignación hoy primero, luego menos cargados
            emp_sorted = sorted(
                emps,
                key=lambda e: (
                    0 if d not in estados[str(e.id)].dias_trabajados else 1,
                    estados[str(e.id)].minutos_semana,
                ),
            )

            for emp in emp_sorted:
                eid = str(emp.id)
                estado = estados[eid]

                if emp.off(d) or emp.absent_day(d):
                    continue
                if d not in estado.dias_trabajados and len(estado.dias_trabajados) >= max_dias:
                    continue

                existing_ivs = sorted(estado.intervalos_por_dia.get(d, []))
                merged_existing = _merge_intervals(existing_ivs)
                has_block = bool(merged_existing)

                # Elegibles: skill + ventana + UserShift (sin historial)
                eligible = [
                    dm
                    for dm in day_unmet
                    if remaining.get(dm.id, 0) > 0
                    and emp.can(dm.wsid)
                    and emp.available(d, dm.start, dm.end)
                    and self.validador._usershift_ok(emp, d, dm.start, dm.end, overrides)
                ]
                if not eligible:
                    continue

                eligible_sorted = sorted(eligible, key=lambda dm: _t2m(dm.start))

                if has_block:
                    # CASO A — Extender bloque existente
                    for blk_s, blk_e in merged_existing:
                        # Forward: demandas contiguas después del bloque
                        fwd: List = []
                        cur_e = blk_e
                        for dm in eligible_sorted:
                            if _t2m(dm.start) == cur_e and remaining.get(dm.id, 0) > 0:
                                fwd.append(dm)
                                cur_e = _end_min(dm.end)
                        if fwd:
                            c_s = _t2m(fwd[0].start)
                            c_e = _end_min(fwd[-1].end)
                            plans.append(
                                CandidatePlan(
                                    emp=emp,
                                    d=d,
                                    plan_type="EXTEND",
                                    chain=fwd,
                                    chain_s=c_s,
                                    chain_e=c_e,
                                    chain_dur=c_e - c_s,
                                )
                            )
                            candidates_generated += 1

                        # Backward: demandas contiguas antes del bloque
                        bwd: List = []
                        cur_s = blk_s
                        for dm in reversed(eligible_sorted):
                            if _end_min(dm.end) == cur_s and remaining.get(dm.id, 0) > 0:
                                bwd.insert(0, dm)
                                cur_s = _t2m(dm.start)
                        if bwd:
                            c_s = _t2m(bwd[0].start)
                            c_e = _end_min(bwd[-1].end)
                            plans.append(
                                CandidatePlan(
                                    emp=emp,
                                    d=d,
                                    plan_type="EXTEND",
                                    chain=bwd,
                                    chain_s=c_s,
                                    chain_e=c_e,
                                    chain_dur=c_e - c_s,
                                )
                            )
                            candidates_generated += 1

                    # CASO B — Segundo bloque partido (si max_bloques permite)
                    if len(merged_existing) < max_bloques:
                        split_chains = self._build_chains_for_employee_day(
                            emp,
                            estado,
                            d,
                            eligible_sorted,
                            min_blk_min,
                        )
                        for chain, chain_dur, _ in split_chains:
                            c_s = _t2m(chain[0].start)
                            c_e = _end_min(chain[-1].end)
                            # Verificar gap mínimo con cada bloque existente
                            gap_ok = True
                            for blk_s, blk_e in merged_existing:
                                g = c_s - blk_e if c_s >= blk_e else blk_s - c_e
                                if 0 <= g < min_gap_split:
                                    gap_ok = False
                                    break
                            if not gap_ok:
                                continue
                            plans.append(
                                CandidatePlan(
                                    emp=emp,
                                    d=d,
                                    plan_type="SPLIT",
                                    chain=chain,
                                    chain_s=c_s,
                                    chain_e=c_e,
                                    chain_dur=chain_dur,
                                )
                            )
                            candidates_generated += 1
                else:
                    # CASO C — Nuevo bloque desde cero
                    new_chains = self._build_chains_for_employee_day(
                        emp,
                        estado,
                        d,
                        eligible_sorted,
                        min_blk_min,
                    )
                    for chain, chain_dur, _ in new_chains:
                        c_s = _t2m(chain[0].start)
                        c_e = _end_min(chain[-1].end)
                        plans.append(
                            CandidatePlan(
                                emp=emp,
                                d=d,
                                plan_type="NEW",
                                chain=chain,
                                chain_s=c_s,
                                chain_e=c_e,
                                chain_dur=chain_dur,
                            )
                        )
                        candidates_generated += 1

            # ── 3. Puntuar (historia como bonus) y ordenar ──
            for plan in plans:
                plan.score = self._score_gap_plan(plan, estados, cov, modelo)
            plans.sort(key=lambda p: -p.score)

            # ── 4. Aplicar greedy con rollback atómico ──
            for plan in plans:
                if any(dm.id in committed for dm in plan.chain):
                    continue
                if any(remaining.get(dm.id, 0) <= 0 for dm in plan.chain):
                    continue

                eid = str(plan.emp.id)
                _chain_ws_ids = {str(dm.wsid) for dm in plan.chain}
                for _wid in _chain_ws_ids:
                    ws_candidates_attempted[_wid] += 1

                ok, reason = self._validate_chain_for_employee(
                    plan.emp,
                    plan.chain,
                    d,
                    estados[eid],
                    overrides,
                    min_blk_min,
                )
                if not ok:
                    reject_counts[reason] += 1
                    for _wid in _chain_ws_ids:
                        reject_by_ws[_wid][reason] += 1
                        ws_candidates_rejected[_wid] += 1
                    reject_by_day[d][reason] += 1
                    if reason == "MAX_HORAS_DIA":
                        emp_rejected_max_hours.add(eid)
                    elif reason == "SOLAPAMIENTO":
                        emp_rejected_overlap.add(eid)
                    continue

                applied_list: List[Tuple[Any, Any, int, int]] = []
                rollback = False
                for dm in plan.chain:
                    try:
                        self._asignar(plan.emp, dm, sched, estados, cov, remaining)
                        applied_list.append((plan.emp, dm, _t2m(dm.start), _end_min(dm.end)))
                    except Exception:
                        rollback = True
                        break

                if rollback:
                    for emp_r, dm_r, s_r, e_r in reversed(applied_list):
                        estados[str(emp_r.id)].desregistrar(d, str(dm_r.wsid), s_r, e_r)
                        remaining[dm_r.id] = remaining.get(dm_r.id, 0) + 1
                        cov[dm_r.id]["covered"] = max(0, cov[dm_r.id]["covered"] - 1)
                        cov[dm_r.id]["met"] = max(0, cov[dm_r.id]["met"] - 1)
                        cov[dm_r.id]["unmet"] += 1
                        sched[d] = [
                            (e2, dm2) for e2, dm2 in sched[d] if not (str(e2.id) == str(emp_r.id) and dm2.id == dm_r.id)
                        ]
                    continue

                for dm in plan.chain:
                    committed.add(dm.id)
                candidates_applied += 1
                employees_used.add(eid)
                plan_types_applied[plan.plan_type] += 1

        # ── 5. Métricas finales ──
        gaps_after = sum(max(0, v) for v in remaining.values())
        slots_added = sum(cs["covered"] for cs in cov.values()) - cov_before
        elapsed_ms = int((_time.time() - t0) * 1000)

        # Verificar bloques cortos restantes (debe ser 0)
        final_short = 0
        for d_key in sched:
            by_emp_d: Dict[str, List] = defaultdict(list)
            for emp, dm in sched[d_key]:
                if dm.wsid is not None:
                    by_emp_d[str(emp.id)].append((emp, dm))
            for _, pairs in by_emp_d.items():
                for blk in self._get_contiguous_blocks_for_employee_day(pairs):
                    if blk["duration_min"] < min_blk_min:
                        final_short += 1

        self._log(
            f"[GAP-FILLER] candidates={candidates_generated} | applied={candidates_applied} | "
            f"slots_added={slots_added} | employees_used={len(employees_used)} | "
            f"extend_block={plan_types_applied.get('EXTEND', 0)} | "
            f"second_split={plan_types_applied.get('SPLIT', 0)} | "
            f"new_block={plan_types_applied.get('NEW', 0)} | "
            f"final_short_blocks={final_short} | time={elapsed_ms}ms"
        )
        for reason, count in reject_counts.most_common():
            self._log(f"[GAP-FILLER-REJECT] reason={reason} count={count}")

        # ── Construir diagnóstico extendido ───────────────────────────────────
        ws_unmet_slots: Dict[str, int] = defaultdict(int)
        for dm in demands:
            if dm.wsid is not None and remaining.get(dm.id, 0) > 0:
                ws_unmet_slots[str(dm.wsid)] += 1

        _CAUSE_MAP = {
            "MAX_HORAS_DIA": "DAILY_HOURS_SATURATION",
            "MAX_HORAS_SEMANALES": "WEEKLY_HOURS_SATURATION",
            "SOLAPAMIENTO": "OVERLAP_CONFLICT",
            "FUERA_USERSHIFT_WINDOW": "USER_SHIFT_RESTRICTION",
            "FUERA_VENTANA": "AVAILABILITY_RESTRICTION",
            "DIA_LIBRE": "AVAILABILITY_RESTRICTION",
            "BLOQUE_CORTO_PROVISIONAL": "MIN_BLOCK_CONSTRAINT",
            "DURACION_MIN": "MIN_BLOCK_CONSTRAINT",
        }

        workstations_diag: List[Dict] = []
        for _wid, _unmet in sorted(ws_unmet_slots.items(), key=lambda x: -x[1]):
            _wname = ws_diag_name.get(_wid, _wid)
            _qualified = len(ws_qualified_emps.get(_wid, set()))
            _attempted = ws_candidates_attempted.get(_wid, 0)
            _rejected = ws_candidates_rejected.get(_wid, 0)
            _ws_rej = reject_by_ws.get(_wid, Counter())
            _top_r = _ws_rej.most_common(1)[0][0] if _ws_rej else None
            # Determinar causa probable
            if _attempted == 0:
                _cause = "SKILL_BOTTLENECK" if _qualified == 0 else "AVAILABILITY_RESTRICTION"
            elif _top_r and _top_r in _CAUSE_MAP:
                _cause = _CAUSE_MAP[_top_r]
            elif _qualified <= 3:
                _cause = "SKILL_BOTTLENECK"
            else:
                _cause = "DAILY_HOURS_SATURATION"
            workstations_diag.append(
                {
                    "workstation_id": _wid,
                    "workstation_name": _wname,
                    "unmet_slots": _unmet,
                    "qualified_employees_count": _qualified,
                    "candidates_attempted": _attempted,
                    "candidates_rejected": _rejected,
                    "top_reject_reason": _top_r,
                    "likely_cause": _cause,
                }
            )

        skills_bottleneck: List[Dict] = [
            {
                "workstation_id": _wid,
                "workstation_name": ws_diag_name.get(_wid, _wid),
                "qualified_count": len(_es),
            }
            for _wid, _es in sorted(ws_qualified_emps.items(), key=lambda x: len(x[1]))
            if ws_unmet_slots.get(_wid, 0) > 0
        ]

        _recommendations: List[str] = []
        if reject_counts:
            _dom = reject_counts.most_common(1)[0][0]
            if _dom == "MAX_HORAS_DIA":
                _recommendations.append(
                    "Los empleados habilitados ya están saturados en horas diarias; "
                    "considerar añadir personal o redistribuir franjas horarias."
                )
            elif _dom == "SOLAPAMIENTO":
                _recommendations.append(
                    "Los empleados habilitados ya están asignados en franjas coincidentes; "
                    "no hay ventanas libres para cubrir los huecos."
                )
            elif _dom == "FUERA_USERSHIFT_WINDOW":
                _recommendations.append(
                    "Revisar ventanas/turnos configurados: las restricciones de turno "
                    "bloquean asignaciones válidas en los huecos detectados."
                )
            elif _dom in ("BLOQUE_CORTO_PROVISIONAL", "DURACION_MIN"):
                _recommendations.append(
                    "No hay cadenas suficientes para formar bloques mínimos válidos; "
                    "considerar reducir min_duracion_turno_horas si la operativa lo permite."
                )
        for _wid, _es in ws_qualified_emps.items():
            if ws_unmet_slots.get(_wid, 0) > 0 and len(_es) <= 5:
                _wname = ws_diag_name.get(_wid, _wid)
                _recommendations.append(
                    f"Habilitar/capacitar más empleados para '{_wname}' " f"(actualmente {len(_es)} habilitados)."
                )

        diagnostics: Dict = {
            "candidates_total": candidates_generated,
            "applied_total": candidates_applied,
            "slots_added": slots_added,
            "top_reject_reasons": dict(reject_counts.most_common(10)),
            "reject_reasons_by_workstation": {_wid: dict(_ctr) for _wid, _ctr in reject_by_ws.items()},
            "reject_reasons_by_day": {str(_dk): dict(_ctr) for _dk, _ctr in reject_by_day.items()},
            "workstations_with_most_unfilled_slots": workstations_diag,
            "employees_rejected_by_max_hours_day": sorted(emp_rejected_max_hours),
            "employees_rejected_by_overlap": sorted(emp_rejected_overlap),
            "skills_bottleneck_summary": skills_bottleneck,
            "operational_recommendations": _recommendations,
        }

        return {
            "gaps_before": gaps_before,
            "gaps_after": gaps_after,
            "slots_added": slots_added,
            "employees_used": len(employees_used),
            "candidate_plans_generated": candidates_generated,
            "candidate_plans_applied": candidates_applied,
            "by_plan_type": dict(plan_types_applied),
            "top_reject_reasons": dict(reject_counts.most_common(10)),
            "final_short_blocks": final_short,
            "underutilized_employees_before": unassigned_before,
            "underutilized_employees_after": _count_unassigned(),
            "one_day_assigned_before": one_day_before,
            "one_day_assigned_after": _count_one_day(),
            "execution_time_ms": elapsed_ms,
            "gap_filler_diagnostics": diagnostics,
        }
