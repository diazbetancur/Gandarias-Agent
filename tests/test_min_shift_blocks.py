# tests/test_min_shift_blocks.py
"""
Pruebas para la validación corregida de bloques mínimos de 3h.

Cubren:
  1. Bloque contiguo multi-workstation ≥ 3h → se conserva completo.
  2. Único bloque < 3h → se elimina.
  3. Split shift: bloque corto + bloque válido → se elimina solo el corto.
  4. No over-removal: bloque corto de un empleado no afecta al otro.
  5. Recuperación: demanda adyacente extiende bloque hasta ≥ 3h.
  6. Recuperación falla si el empleado no tiene el skill.
  7. Recuperación falla si viola la ventana de UserShift.
  8. Filtro final detecta bloques < 3h post-RELAX.
  9. Horario final sin bloques < 3h (integración generar()).
  10. Cobertura no cae por over-removal en split shift.

Ejecutar con:
    pytest tests/test_min_shift_blocks.py -v
"""

from __future__ import annotations

from collections import defaultdict
from datetime import date, time
from typing import Dict, List, Optional, Set
from uuid import uuid4

import pytest

from services.ai_scheduler import (
    AIScheduleGenerator,
    EstadoEmpleado,
    ModeloPatrones,
    REGLAS_DURAS_DEFAULTS,
    _t2m,
    _end_min,
)

# ─────────────────────────────────────────────────────────────────────────────
# MOCKS MÍNIMOS  (misma interfaz que test_repair_engine.py)
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
        ws_name: str = "",
    ):
        self.id = id_str
        self.date = d
        self.wsid = ws_id
        self.wsname = ws_name or ws_id
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
# HELPERS
# ─────────────────────────────────────────────────────────────────────────────

REGLAS = dict(REGLAS_DURAS_DEFAULTS)  # min_duracion_turno_horas = 3
DAY = date(2026, 5, 25)  # Lunes


def _make_gen() -> AIScheduleGenerator:
    return AIScheduleGenerator(ModeloPatrones(), reglas=dict(REGLAS), debug=False)


def _make_estado(emp_id: str, intervals_day: List[tuple] = None) -> EstadoEmpleado:
    """Crea un EstadoEmpleado con intervalos ya registrados."""
    est = EstadoEmpleado(emp_id=emp_id)
    for s, e in intervals_day or []:
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


def _make_remaining(demands, pending=0):
    return {dm.id: pending for dm in demands}


def _run_filter(gen, sched, estados, cov, remaining, emps=None, demands=None, overrides=None, label="3H-FILTER"):
    """Llama a _filtrar_bloques_cortos y retorna la tupla completa."""
    return gen._filtrar_bloques_cortos(
        sched,
        estados,
        cov,
        remaining,
        emps=emps,
        demands=demands,
        overrides=overrides or set(),
        label=label,
    )


# ─────────────────────────────────────────────────────────────────────────────
# TEST 1: Bloque contiguo multi-workstation ≥ 3h → todo se conserva
# ─────────────────────────────────────────────────────────────────────────────


def test_min_shift_keeps_contiguous_multi_workstation_block():
    """
    10:30-11:00 APERTURA + 11:00-12:00 CAMARERO + 12:00-18:00 ENLACE
    Mismo empleado, mismo día. Bloque continuo = 7.5h → debe conservarse completo.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-apertura", "ws-camarero", "ws-enlace"})

    dm1 = MockDemand("d1", DAY, "ws-apertura", time(10, 30), time(11, 0))
    dm2 = MockDemand("d2", DAY, "ws-camarero", time(11, 0), time(12, 0))
    dm3 = MockDemand("d3", DAY, "ws-enlace", time(12, 0), time(18, 0))

    demands = [dm1, dm2, dm3]
    sched = defaultdict(list)
    sched[DAY] = [(emp, dm1), (emp, dm2), (emp, dm3)]

    # Estado con los tres intervalos registrados
    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(11, 0)))
    estado.registrar(DAY, "ws-camarero", _t2m(time(11, 0)), _end_min(time(12, 0)))
    estado.registrar(DAY, "ws-enlace", _t2m(time(12, 0)), _end_min(time(18, 0)))
    estados = {"A": estado}

    cov = _make_cov(demands)
    remaining = _make_remaining(demands, 0)

    removed_slots, recovered, removed_blocks, preserved = _run_filter(gen, sched, estados, cov, remaining)

    assert removed_slots == 0, "No debe eliminar ningún slot"
    assert len(sched[DAY]) == 3, "Los 3 segmentos deben conservarse"
    assert preserved == 1, "El bloque continuo cuenta como 1 bloque válido"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 2: Único bloque < 3h → se elimina
# ─────────────────────────────────────────────────────────────────────────────


def test_short_block_removed_when_only_block_under_3h():
    """
    Empleado con única asignación 10:30-12:00 = 1.5h → debe eliminarse.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-apertura"})
    dm1 = MockDemand("d1", DAY, "ws-apertura", time(10, 30), time(12, 0))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm1)]

    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(12, 0)))
    estados = {"A": estado}

    cov = _make_cov([dm1])
    remaining = _make_remaining([dm1], 0)

    removed_slots, recovered, removed_blocks, _ = _run_filter(gen, sched, estados, cov, remaining)

    assert removed_slots == 1, "El slot corto debe eliminarse"
    assert removed_blocks == 1
    assert len(sched[DAY]) == 0
    assert cov["d1"]["covered"] == 0
    assert remaining["d1"] == 1


# ─────────────────────────────────────────────────────────────────────────────
# TEST 3: Split shift — elimina solo el bloque corto, conserva el válido
# ─────────────────────────────────────────────────────────────────────────────


def test_split_shift_preserves_valid_long_block():
    """
    Bloque 1: 10:30-12:00 = 1.5h (corto) → eliminar
    Bloque 2: 17:00-22:00 = 5h (válido) → conservar
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-apertura", "ws-enlace"})

    dm_short = MockDemand("d_short", DAY, "ws-apertura", time(10, 30), time(12, 0))
    dm_long = MockDemand("d_long", DAY, "ws-enlace", time(17, 0), time(22, 0))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm_short), (emp, dm_long)]

    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(12, 0)))
    estado.registrar(DAY, "ws-enlace", _t2m(time(17, 0)), _end_min(time(22, 0)))
    estados = {"A": estado}

    cov = _make_cov([dm_short, dm_long])
    remaining = _make_remaining([dm_short, dm_long], 0)

    removed_slots, recovered, removed_blocks, preserved = _run_filter(gen, sched, estados, cov, remaining)

    assert removed_slots == 1, "Solo el bloque corto se elimina"
    assert removed_blocks == 1
    assert preserved == 1, "El bloque largo queda como válido"

    day_assignments = sched[DAY]
    ws_ids = {dm.wsid for _, dm in day_assignments}
    assert "ws-enlace" in ws_ids, "El bloque largo debe conservarse"
    assert "ws-apertura" not in ws_ids, "El bloque corto debe eliminarse"

    # Estado del empleado debe reflejar solo el bloque largo
    assert (10 * 60 + 30, 12 * 60) not in estado.intervalos_por_dia.get(DAY, [])
    assert (17 * 60, 22 * 60) in estado.intervalos_por_dia.get(DAY, [])


# ─────────────────────────────────────────────────────────────────────────────
# TEST 4: No over-removal — bloque corto de Emp A no afecta a Emp B
# ─────────────────────────────────────────────────────────────────────────────


def test_no_over_removal_by_employee_day():
    """
    Emp A: 10:30-12:00 (corto) → se elimina
    Emp B: 12:00-18:00 (válido) → NO se toca
    """
    gen = _make_gen()
    empA = MockEmp("A", {"ws-apertura"})
    empB = MockEmp("B", {"ws-enlace"})

    dm_a = MockDemand("da", DAY, "ws-apertura", time(10, 30), time(12, 0))
    dm_b = MockDemand("db", DAY, "ws-enlace", time(12, 0), time(18, 0))

    sched = defaultdict(list)
    sched[DAY] = [(empA, dm_a), (empB, dm_b)]

    estA = EstadoEmpleado(emp_id="A")
    estA.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(12, 0)))
    estB = EstadoEmpleado(emp_id="B")
    estB.registrar(DAY, "ws-enlace", _t2m(time(12, 0)), _end_min(time(18, 0)))
    estados = {"A": estA, "B": estB}

    cov = _make_cov([dm_a, dm_b])
    remaining = _make_remaining([dm_a, dm_b], 0)

    removed_slots, _, removed_blocks, preserved = _run_filter(gen, sched, estados, cov, remaining)

    assert removed_slots == 1
    assert removed_blocks == 1
    assert preserved == 1

    day_ws = {dm.wsid for _, dm in sched[DAY]}
    assert "ws-enlace" in day_ws, "Emp B debe conservarse"
    assert "ws-apertura" not in day_ws, "Emp A debe eliminarse"
    assert cov["db"]["covered"] == 1, "Cobertura de Emp B intacta"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 5: Recuperación exitosa — demanda adyacente extiende a ≥ 3h
# ─────────────────────────────────────────────────────────────────────────────


def test_short_block_recovery_extends_adjacent_gap():
    """
    Empleado tiene 10:30-12:00 (90 min, corto).
    Existe demanda no cubierta 12:00-13:30 (90 min) que el empleado puede cubrir.
    → Bloque final: 10:30-13:30 = 3h → recuperado, todo se conserva.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-apertura", "ws-comedor"})

    dm_short = MockDemand("d_short", DAY, "ws-apertura", time(10, 30), time(12, 0))
    dm_extend = MockDemand("d_extend", DAY, "ws-comedor", time(12, 0), time(13, 30))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm_short)]

    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(12, 0)))
    estados = {"A": estado}

    cov = _make_cov([dm_short, dm_extend])
    cov["d_extend"]["covered"] = 0  # Demanda extension no cubierta
    cov["d_extend"]["met"] = 0
    cov["d_extend"]["unmet"] = 1
    remaining = {"d_short": 0, "d_extend": 1}  # d_extend disponible

    removed_slots, recovered, removed_blocks, preserved = _run_filter(
        gen,
        sched,
        estados,
        cov,
        remaining,
        emps=[emp],
        demands=[dm_short, dm_extend],
    )

    assert recovered == 1, "El bloque debe recuperarse"
    assert removed_slots == 0
    assert removed_blocks == 0

    # La asignación de extensión debe estar en el horario
    day_ws = {dm.wsid for _, dm in sched[DAY]}
    assert "ws-apertura" in day_ws
    assert "ws-comedor" in day_ws

    # La extensión ya no tiene remaining
    assert remaining["d_extend"] == 0
    assert cov["d_extend"]["covered"] == 1


# ─────────────────────────────────────────────────────────────────────────────
# TEST 6: Recuperación falla si el empleado no tiene el skill
# ─────────────────────────────────────────────────────────────────────────────


def test_short_block_recovery_rejects_if_no_skill():
    """
    Empleado solo tiene skill para ws-apertura, no para ws-cocina.
    La única demanda adyacente es ws-cocina → no puede extender → bloque eliminado.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-apertura"})  # Sin ws-cocina

    dm_short = MockDemand("d_short", DAY, "ws-apertura", time(10, 30), time(12, 0))
    dm_extend = MockDemand("d_extend", DAY, "ws-cocina", time(12, 0), time(13, 30))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm_short)]

    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(12, 0)))
    estados = {"A": estado}

    cov = _make_cov([dm_short, dm_extend])
    cov["d_extend"]["covered"] = 0
    cov["d_extend"]["met"] = 0
    cov["d_extend"]["unmet"] = 1
    remaining = {"d_short": 0, "d_extend": 1}

    removed_slots, recovered, removed_blocks, _ = _run_filter(
        gen,
        sched,
        estados,
        cov,
        remaining,
        emps=[emp],
        demands=[dm_short, dm_extend],
    )

    assert recovered == 0, "No debe recuperar (sin skill)"
    assert removed_slots == 1, "El bloque corto debe eliminarse"
    assert removed_blocks == 1
    assert remaining["d_extend"] == 1, "La demanda adjunta no debe consumirse"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 7: Recuperación falla si viola la ventana de UserShift
# ─────────────────────────────────────────────────────────────────────────────


def test_short_block_recovery_rejects_if_violates_usershift():
    """
    Empleado tiene UserShift solo de 10:00-12:00 (lunes).
    Tiene bloque 10:30-12:00 (corto). Demanda adjunta 12:00-13:30 viola la ventana.
    → Recuperación falla → bloque eliminado.
    """
    gen = _make_gen()
    # DOW 0 = Lunes, ventana solo hasta 12:00
    emp = MockEmp(
        "A",
        {"ws-apertura", "ws-comedor"},
        windows_by_dow={0: [(time(10, 0), time(12, 0))]},
    )
    emp.user_shift_windows = {0: [(time(10, 0), time(12, 0))]}  # para _usershift_ok

    dm_short = MockDemand("d_short", DAY, "ws-apertura", time(10, 30), time(12, 0))
    dm_extend = MockDemand("d_extend", DAY, "ws-comedor", time(12, 0), time(13, 30))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm_short)]

    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(12, 0)))
    estados = {"A": estado}

    cov = _make_cov([dm_short, dm_extend])
    cov["d_extend"]["covered"] = 0
    cov["d_extend"]["met"] = 0
    cov["d_extend"]["unmet"] = 1
    remaining = {"d_short": 0, "d_extend": 1}

    removed_slots, recovered, removed_blocks, _ = _run_filter(
        gen,
        sched,
        estados,
        cov,
        remaining,
        emps=[emp],
        demands=[dm_short, dm_extend],
    )

    assert recovered == 0, "No debe recuperar (viola UserShift)"
    assert removed_slots == 1
    assert removed_blocks == 1


# ─────────────────────────────────────────────────────────────────────────────
# TEST 8: Filtro final detecta bloques < 3h post-RELAX
# ─────────────────────────────────────────────────────────────────────────────


def test_final_filter_runs_after_relax4():
    """
    Simula que RELAX-4 creó un bloque de 2h (pasó el filtro previo porque
    min_turno estaba en 2h temporal). Al llamar _filtrar_bloques_cortos de
    nuevo con la regla real (3h), el bloque debe detectarse y eliminarse.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-apertura"})
    # Bloque de 2h — pasó el filtro previo, pero la regla real es 3h
    dm = MockDemand("d1", DAY, "ws-apertura", time(10, 0), time(12, 0))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm)]

    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 0)), _end_min(time(12, 0)))
    estados = {"A": estado}

    cov = _make_cov([dm])
    remaining = _make_remaining([dm], 0)

    removed_slots, _, removed_blocks, _ = _run_filter(gen, sched, estados, cov, remaining, label="FINAL-3H")

    assert removed_slots == 1, "El bloque de 2h debe detectarse en el filtro final"
    assert removed_blocks == 1
    assert len(sched[DAY]) == 0


# ─────────────────────────────────────────────────────────────────────────────
# TEST 9: Horario final generado no contiene bloques < 3h (integración)
# ─────────────────────────────────────────────────────────────────────────────


def test_final_schedule_has_no_blocks_under_3h():
    """
    Integración mínima con generar(). Configura demands de una semana y verifica
    que el horario resultante no tenga ningún empleado con bloque continuo < 3h.
    """
    gen = _make_gen()
    week = [date(2026, 5, 25) + __import__("datetime").timedelta(days=i) for i in range(7)]

    # 1 empleado con skill para un workstation
    emp = MockEmp("A", {"ws-barra"}, weekly_minutes=40 * 60)

    # Una sola demanda de 4h en lunes (debe asignarse y conservarse)
    dm = MockDemand("d1", week[0], "ws-barra", time(10, 0), time(14, 0))

    sched, coverage_stats, _ = gen.generar([emp], [dm], week)

    # Verificar no hay bloques < 3h en el resultado
    min_blk_min = gen.reglas.get("min_duracion_turno_horas", 3) * 60
    for d, assignments in sched.items():
        by_emp = defaultdict(list)
        for emp_a, dm_a in assignments:
            if dm_a.wsid is not None:
                by_emp[str(emp_a.id)].append((emp_a, dm_a))
        for eid, pairs in by_emp.items():
            blocks = gen._get_contiguous_blocks_for_employee_day(pairs)
            for blk in blocks:
                assert blk["duration_min"] >= min_blk_min, (
                    f"Bloque < 3h en empleado {eid} día {d}: "
                    f"{blk['start_min']//60:02d}:{blk['start_min']%60:02d}-"
                    f"{blk['end_min']//60:02d}:{blk['end_min']%60:02d} "
                    f"= {blk['duration_min']/60:.1f}h"
                )


# ─────────────────────────────────────────────────────────────────────────────
# TEST 10: Cobertura no cae por over-removal en split shift
# ─────────────────────────────────────────────────────────────────────────────


def test_coverage_does_not_drop_due_to_over_removal():
    """
    Empleado con split shift: bloque corto (1.5h) + bloque válido (5h).
    Con la lógica corregida, solo se elimina el bloque corto y la cobertura
    del bloque largo se conserva.
    Con la lógica antigua, se eliminaban AMBOS bloques y la cobertura caía.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-apertura", "ws-enlace"})

    dm_short = MockDemand("d_short", DAY, "ws-apertura", time(10, 30), time(12, 0))
    dm_long = MockDemand("d_long", DAY, "ws-enlace", time(17, 0), time(22, 0))

    sched = defaultdict(list)
    sched[DAY] = [(emp, dm_short), (emp, dm_long)]

    estado = EstadoEmpleado(emp_id="A")
    estado.registrar(DAY, "ws-apertura", _t2m(time(10, 30)), _end_min(time(12, 0)))
    estado.registrar(DAY, "ws-enlace", _t2m(time(17, 0)), _end_min(time(22, 0)))
    estados = {"A": estado}

    cov = _make_cov([dm_short, dm_long])
    remaining = _make_remaining([dm_short, dm_long], 0)

    removed_slots, recovered, removed_blocks, preserved = _run_filter(gen, sched, estados, cov, remaining)

    # Solo 1 bloque eliminado (el corto), 1 conservado (el largo)
    assert removed_blocks == 1
    assert preserved == 1
    assert removed_slots == 1

    # Cobertura del bloque largo intacta
    assert cov["d_long"]["covered"] == 1, "La cobertura del bloque largo debe conservarse con la lógica corregida"
    assert cov["d_short"]["covered"] == 0
