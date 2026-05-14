# tests/test_strict_min_shift.py
"""
Pruebas para el modo estricto allow_short_block_provisional=False
introducido para eliminar el ciclo FINAL-3H / POST-FINAL-3H.

Cubren:
  1. Fase constructiva: provisional tolerado (allow=True, comportamiento original).
  2. Fase final: provisional rechazado (allow=False, nuevo BLOQUE_CORTO_FINAL).
  3. POST-FINAL-3H estricto no reintroduce bloques cortos.
  4. Modo estricto permite agregar si bloque resultante queda >= 3h.
  5. Modo estricto rechaza si bloque resultante queda < 3h.
  6. Horario final sin bloques < 3h (integración generar()).

Ejecutar con:
    pytest tests/test_strict_min_shift.py -v
"""

from __future__ import annotations

from collections import defaultdict
from datetime import date, time
from typing import Dict, List, Optional, Set

import pytest

from services.ai_scheduler import (
    AIScheduleGenerator,
    EstadoEmpleado,
    ModeloPatrones,
    REGLAS_DURAS_DEFAULTS,
    ValidadorReglasDuras,
    _t2m,
    _end_min,
)

# ─────────────────────────────────────────────────────────────────────────────
# MOCKS MÍNIMOS (misma interfaz que test_repair_engine.py)
# ─────────────────────────────────────────────────────────────────────────────


class MockEmp:
    def __init__(
        self,
        id_str: str,
        roles: Set[str],
        weekly_minutes: int = 40 * 60,
        day_off: Optional[Set[int]] = None,
        absent: Optional[Set[date]] = None,
        windows_by_dow: Optional[Dict] = None,
    ):
        self.id = id_str
        self.name = f"Emp-{id_str}"
        self.roles = set(roles)
        self.roles_originales = set(roles)
        self.day_off = set(day_off or [])
        self.absent = set(absent or [])
        self.window: Dict = defaultdict(list)
        if windows_by_dow:
            for dow, wins in windows_by_dow.items():
                self.window[dow] = wins
        self.exc: Dict = defaultdict(list)
        self._weekly_minutes = weekly_minutes
        self.user_shift_windows: Dict = defaultdict(list)
        self.split = False
        self.complement_hours = False
        self.law_apply = False
        self.extra_hours = False
        self.cant_part_time_schedule = 0
        self.hired_hours = weekly_minutes / 60

    def can(self, ws) -> bool:
        return str(ws) in {str(r) for r in self.roles}

    def off(self, d: date) -> bool:
        return d.weekday() in self.day_off

    def absent_day(self, d: date) -> bool:
        return d in self.absent

    def available(self, d: date, s: time, e: time) -> bool:
        if self.off(d) or self.absent_day(d):
            return False
        win = self.exc.get(d) or self.window.get(d.weekday(), [])
        if not win:
            if self.window:
                return False
            return True
        end = e if e != time(0, 0) else time(23, 59)
        for a, b in win:
            b2 = b if b != time(0, 0) else time(23, 59)
            if s >= a and end <= b2:
                return True
        return False

    def weekly_hours_limit(self) -> int:
        return self._weekly_minutes


class MockDemand:
    def __init__(
        self,
        id_str: str,
        d: date,
        ws_id: str,
        start: time,
        end: time,
        need: int = 1,
    ):
        self.id = id_str
        self.date = d
        self.wsid = ws_id
        self.wsname = ws_id
        self.start = start
        self.end = end
        self.need = need
        self.raw_need = float(need)
        self.has_hybrid_component = False
        self.observation_override = None
        self.hybrid_group_id = None
        self.hybrid_partner_wsid = None
        self.slot_index = 0
        self.shift_type = None


# ─────────────────────────────────────────────────────────────────────────────
# FIXTURES
# ─────────────────────────────────────────────────────────────────────────────

REGLAS = dict(REGLAS_DURAS_DEFAULTS)  # min_duracion_turno_horas=3
DAY = date(2026, 5, 25)  # Lunes


def _make_validador() -> ValidadorReglasDuras:
    return ValidadorReglasDuras(dict(REGLAS))


def _make_gen() -> AIScheduleGenerator:
    return AIScheduleGenerator(ModeloPatrones(), reglas=dict(REGLAS), debug=False)


def _estado_con_intervalo(emp_id: str, s: int, e: int) -> EstadoEmpleado:
    """Estado con un intervalo ya registrado para DAY."""
    est = EstadoEmpleado(emp_id=emp_id)
    est.registrar(DAY, "ws-dummy", s, e)
    return est


def _make_cov(demands):
    cov = {}
    for dm in demands:
        cov[dm.id] = {
            "demand": dm,
            "met": dm.need,
            "covered": dm.need,
            "unmet": 0,
            "coverage_pct": 100.0,
            "employees": [],
        }
    return cov


# ─────────────────────────────────────────────────────────────────────────────
# TEST 1: Fase constructiva — bloque provisional tolerado con allow=True
# ─────────────────────────────────────────────────────────────────────────────


def test_constructive_phase_allows_provisional_short_block():
    """
    Con allow_short_block_provisional=True (default) y existing_day_min > 0,
    puede_asignar debe PERMITIR agregar un segmento aunque el bloque resultante
    sea < 3h (comportamiento original de fase constructiva).
    """
    v = _make_validador()
    emp = MockEmp("A", {"ws-barra"})

    # Estado: empleado ya tiene 2h asignadas hoy (18:00-20:00)
    estado = _estado_con_intervalo("A", 18 * 60, 20 * 60)

    # Demanda: 12:00-12:30 (30 min), no contigua con la de arriba → bloque aislado
    dm = MockDemand("d1", DAY, "ws-barra", time(12, 0), time(12, 30))

    # Con allow=True (default): se tolera porque existing_day_min > 0
    ok, reason = v.puede_asignar(
        emp,
        dm,
        DAY,
        estado,
        allow_short_block_provisional=True,
    )
    assert ok, f"Fase constructiva debe tolerar bloque corto provisional, got reason={reason}"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 2: Fase final — BLOQUE_CORTO_FINAL con allow=False
# ─────────────────────────────────────────────────────────────────────────────


def test_final_phase_rejects_provisional_short_block():
    """
    Con allow_short_block_provisional=False, un bloque resultante <3h debe
    rechazarse con BLOQUE_CORTO_FINAL aunque existing_day_min > 0.
    """
    v = _make_validador()
    emp = MockEmp("A", {"ws-barra"})

    # Estado: empleado ya tiene 2h asignadas hoy
    estado = _estado_con_intervalo("A", 18 * 60, 20 * 60)

    # Demanda: 12:00-12:30 (30 min) → bloque aislado = 30 min < 3h
    dm = MockDemand("d1", DAY, "ws-barra", time(12, 0), time(12, 30))

    ok, reason = v.puede_asignar(
        emp,
        dm,
        DAY,
        estado,
        allow_short_block_provisional=False,
    )
    assert not ok, "Modo estricto debe rechazar bloque corto final"
    assert reason == "BLOQUE_CORTO_FINAL", f"Se esperaba BLOQUE_CORTO_FINAL, got {reason}"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 3: POST-FINAL-3H estricto no reintroduce bloques cortos
# ─────────────────────────────────────────────────────────────────────────────


def test_post_final_refill_does_not_reintroduce_short_blocks():
    """
    Simula el ciclo que se producía:
    1. FINAL-3H elimina bloque 12:00-12:30 (30 min) del empleado A.
    2. POST-FINAL-3H intenta rellenar la demanda con allow=False.
    3. El empleado A tiene 18:00-20:00 existente → el bloque 12:00-12:30 sería 30 min.
    4. Con modo estricto, el bloque NO se reintroduce.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-barra", "ws-enlace"})

    dm_short = MockDemand("d_short", DAY, "ws-barra", time(12, 0), time(12, 30))
    dm_long = MockDemand("d_long", DAY, "ws-enlace", time(18, 0), time(20, 0))

    # Estado inicial: empleado tiene el bloque largo (FINAL-3H ya eliminó el corto)
    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-enlace", _t2m(time(18, 0)), _end_min(time(20, 0)))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm_long)]  # Solo el largo (el corto fue eliminado)

    cov = _make_cov([dm_short, dm_long])
    cov["d_short"]["covered"] = 0
    cov["d_short"]["met"] = 0
    cov["d_short"]["unmet"] = 1
    remaining = {"d_short": 1, "d_long": 0}

    # Ejecutar _pase_extra en modo estricto
    filled = gen._pase_extra(
        [emp],
        [dm_short, dm_long],
        sched,
        {"A": estado},
        cov,
        remaining,
        set(),
        300.0,
        "POST-FINAL-3H-TEST",
        allow_short_block_provisional=False,
    )

    # El bloque corto no debe haberse agregado
    assert filled == 0, f"Modo estricto no debe agregar el bloque corto, pero filled={filled}"
    day_ws = {dm.wsid for _, dm in sched[DAY]}
    assert "ws-barra" not in day_ws, "ws-barra (bloque corto) no debe estar en el horario"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 4: Modo estricto SÍ permite agregar si el bloque resultante queda ≥ 3h
# ─────────────────────────────────────────────────────────────────────────────


def test_post_final_refill_can_add_slot_if_resulting_block_reaches_3h():
    """
    Con allow=False, puede_asignar DEBE permitir agregar un segmento si
    el bloque mergeado resultante alcanza >= 3h.

    Caso: empleado tiene 12:00-13:30 (90 min). Agregar 13:30-15:00 (90 min)
    produce bloque 12:00-15:00 = 3h = exactamente el mínimo.
    """
    v = _make_validador()
    emp = MockEmp("A", {"ws-barra"})

    # Estado: empleado tiene 12:00-13:30 (90 min)
    estado = _estado_con_intervalo("A", 12 * 60, 13 * 60 + 30)

    # Agregar 13:30-15:00 (90 min) → bloque mergeado = 12:00-15:00 = 180 min = 3h
    dm = MockDemand("d1", DAY, "ws-barra", time(13, 30), time(15, 0))

    ok, reason = v.puede_asignar(
        emp,
        dm,
        DAY,
        estado,
        allow_short_block_provisional=False,
    )
    assert ok, f"Modo estricto debe permitir extensión que lleva bloque a 3h, got reason={reason}"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 5: Modo estricto rechaza si el bloque resultante sigue < 3h
# ─────────────────────────────────────────────────────────────────────────────


def test_post_final_refill_rejects_slot_if_resulting_block_still_under_3h():
    """
    Con allow=False, debe rechazarse un segmento que aunque extiende el bloque
    existente, no lo lleva a >= 3h.

    Caso: empleado tiene 12:00-13:00 (60 min). Agregar 13:00-13:30 (30 min)
    produce bloque 12:00-13:30 = 90 min < 3h.
    """
    v = _make_validador()
    emp = MockEmp("A", {"ws-barra"})

    # Estado: empleado tiene 12:00-13:00 (60 min)
    estado = _estado_con_intervalo("A", 12 * 60, 13 * 60)

    # Agregar 13:00-13:30 (30 min) → bloque mergeado = 12:00-13:30 = 90 min < 3h
    dm = MockDemand("d1", DAY, "ws-barra", time(13, 0), time(13, 30))

    ok, reason = v.puede_asignar(
        emp,
        dm,
        DAY,
        estado,
        allow_short_block_provisional=False,
    )
    assert not ok, "Modo estricto debe rechazar extensión que deja bloque < 3h"
    assert reason == "BLOQUE_CORTO_FINAL", f"Se esperaba BLOQUE_CORTO_FINAL, got {reason}"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 6: Horario final sin bloques < 3h (integración con generar())
# ─────────────────────────────────────────────────────────────────────────────


def test_final_schedule_has_zero_short_blocks():
    """
    Integración con generar(). El horario producido no debe tener ningún empleado
    con bloque continuo < 3h en ningún día.
    Incluye demandas cortas (< 3h) para asegurarse de que el pipeline las gestione.
    """
    import datetime

    gen = _make_gen()

    week = [date(2026, 5, 25) + datetime.timedelta(days=i) for i in range(7)]
    emp = MockEmp("A", {"ws-barra", "ws-comedor"}, weekly_minutes=40 * 60)

    # Una demanda larga (4h) y una corta (1h) el mismo día
    dm_long = MockDemand("d_long", week[0], "ws-barra", time(10, 0), time(14, 0))
    dm_short = MockDemand("d_short", week[0], "ws-comedor", time(15, 0), time(16, 0))

    sched, coverage_stats, _ = gen.generar([emp], [dm_long, dm_short], week)

    min_blk_min = gen.reglas.get("min_duracion_turno_horas", 3) * 60
    violations = []
    for d, assignments in sched.items():
        by_emp = defaultdict(list)
        for emp_a, dm_a in assignments:
            if dm_a.wsid is not None:
                by_emp[str(emp_a.id)].append((emp_a, dm_a))
        for eid, pairs in by_emp.items():
            blocks = gen._get_contiguous_blocks_for_employee_day(pairs)
            for blk in blocks:
                if blk["duration_min"] < min_blk_min:
                    violations.append(
                        f"emp={eid} {d} "
                        f"{blk['start_min']//60:02d}:{blk['start_min']%60:02d}-"
                        f"{blk['end_min']//60:02d}:{blk['end_min']%60:02d} "
                        f"= {blk['duration_min']/60:.1f}h"
                    )

    assert violations == [], f"El horario final contiene {len(violations)} bloque(s) < 3h:\n" + "\n".join(violations)
