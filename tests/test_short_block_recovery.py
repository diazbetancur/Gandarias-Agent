# tests/test_short_block_recovery.py
"""
Pruebas para ShortBlockRecoveryPass:
  _build_chains_for_employee_day
  _validate_chain_for_employee
  _short_block_recovery_pass

Escenarios:
  1.  Construye bloque válido con 3 demandas de 1h
  2.  Rechaza cadena de 2h (< 3h mínimo)
  3.  Rechaza si una demanda viola UserShift
  4.  Rechaza si empleado no tiene skill en una demanda de la cadena
  5.  Prioriza empleado sin asignación ese día
  6.  No deja bloques finales < 3h
  7.  Mejora cobertura sin violaciones duras
  8.  No muta horario si no hay cadenas válidas
  9.  _validate_chain_for_employee cubre todas las reglas duras
  10. generar() con SBR produce final_short_blocks=0

Ejecutar con:
    pytest tests/test_short_block_recovery.py -v
"""

from __future__ import annotations

import datetime
from collections import defaultdict
from datetime import date, time
from typing import Dict, List, Optional, Set

import pytest

from services.ai_scheduler import (
    AIScheduleGenerator,
    EstadoEmpleado,
    ModeloPatrones,
    REGLAS_DURAS_DEFAULTS,
    _end_min,
    _t2m,
)

# ─────────────────────────────────────────────────────────────────────────────
# MOCKS COMPARTIDOS
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
        user_shift_by_dow: Optional[Dict] = None,
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
        if user_shift_by_dow:
            for dow, wins in user_shift_by_dow.items():
                self.user_shift_windows[dow] = wins
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
# FIXTURES COMUNES
# ─────────────────────────────────────────────────────────────────────────────

REGLAS = dict(REGLAS_DURAS_DEFAULTS)  # min_duracion_turno_horas=3, min_gap_split=3
DAY = date(2026, 5, 25)  # Lunes
MIN_BLK_MIN = 3 * 60  # 180 min


def _make_gen() -> AIScheduleGenerator:
    return AIScheduleGenerator(ModeloPatrones(), reglas=dict(REGLAS), debug=False)


def _empty_estado(emp_id: str) -> EstadoEmpleado:
    return EstadoEmpleado(emp_id=emp_id)


def _estado_con_intervalo(emp_id: str, s: int, e: int) -> EstadoEmpleado:
    est = EstadoEmpleado(emp_id=emp_id)
    est.registrar(DAY, "ws-dummy", s, e)
    return est


def _make_cov(demands):
    return {
        dm.id: {
            "demand": dm,
            "met": 0,
            "covered": 0,
            "unmet": dm.need,
            "coverage_pct": 0.0,
            "employees": [],
        }
        for dm in demands
    }


def _make_remaining(demands):
    return {dm.id: dm.need for dm in demands}


# ─────────────────────────────────────────────────────────────────────────────
# TEST 1: Construye bloque válido con 3 demandas de 1h
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_builds_valid_block_from_3_short_demands():
    """
    Tres demandas contiguas de 1h cada una forman una cadena de 3h.
    ShortBlockRecoveryPass debe aplicarlas todas en un solo bloque válido.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-barra"})

    dms = [
        MockDemand("d1", DAY, "ws-barra", time(12, 0), time(13, 0)),
        MockDemand("d2", DAY, "ws-barra", time(13, 0), time(14, 0)),
        MockDemand("d3", DAY, "ws-barra", time(14, 0), time(15, 0)),
    ]
    sched = defaultdict(list)
    estados = {"A": _empty_estado("A")}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    c, a, s, b, r = gen._short_block_recovery_pass([emp], dms, sched, estados, cov, remaining, set())

    assert s == 3, f"Deben agregarse 3 slots, got {s}"
    assert b == 1, f"Debe crearse 1 bloque, got {b}"
    assert a == 1, f"Debe aplicarse 1 cadena, got {a}"
    assert remaining["d1"] == 0
    assert remaining["d2"] == 0
    assert remaining["d3"] == 0
    assert cov["d1"]["covered"] == 1
    assert len(sched[DAY]) == 3


# ─────────────────────────────────────────────────────────────────────────────
# TEST 2: Rechaza cadena de 2h (< 3h)
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_rejects_chain_under_3h():
    """
    Dos demandas de 1h forman 2h total — inferior al mínimo.
    El pase debe rechazarlas y no modificar el horario.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-barra"})

    dms = [
        MockDemand("d1", DAY, "ws-barra", time(12, 0), time(13, 0)),
        MockDemand("d2", DAY, "ws-barra", time(13, 0), time(14, 0)),
    ]
    sched = defaultdict(list)
    estados = {"A": _empty_estado("A")}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    c, a, s, b, r = gen._short_block_recovery_pass([emp], dms, sched, estados, cov, remaining, set())

    assert s == 0, f"No deben agregarse slots para cadenas < 3h, got {s}"
    assert len(sched[DAY]) == 0
    assert remaining["d1"] == 1
    assert remaining["d2"] == 1


# ─────────────────────────────────────────────────────────────────────────────
# TEST 3: Rechaza si una demanda de la cadena viola UserShift
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_rejects_chain_with_usershift_violation():
    """
    El empleado tiene UserShift restringido a 08:00-13:00.
    Una cadena [12:00-13:00, 13:00-14:00, 14:00-15:00] viola el límite en
    la segunda y tercera demanda (13:00+ fuera de ventana).
    El pase no debe aplicar ningún slot.
    """
    gen = _make_gen()
    # UserShift: lunes = 08:00-13:00 solamente
    emp = MockEmp(
        "A",
        {"ws-barra"},
        user_shift_by_dow={0: [(time(8, 0), time(13, 0))]},
    )

    dms = [
        MockDemand("d1", DAY, "ws-barra", time(12, 0), time(13, 0)),
        MockDemand("d2", DAY, "ws-barra", time(13, 0), time(14, 0)),
        MockDemand("d3", DAY, "ws-barra", time(14, 0), time(15, 0)),
    ]
    sched = defaultdict(list)
    estados = {"A": _empty_estado("A")}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    _, _, s, _, _ = gen._short_block_recovery_pass([emp], dms, sched, estados, cov, remaining, set())

    assert s == 0, "La violación de UserShift en parte de la cadena debe rechazar toda la cadena"
    assert len(sched[DAY]) == 0


# ─────────────────────────────────────────────────────────────────────────────
# TEST 4: Rechaza si empleado no tiene skill en una demanda de la cadena
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_rejects_chain_if_no_skill_for_middle_demand():
    """
    El empleado tiene skill para ws-barra pero NO para ws-enlace.
    La cadena [12:00-13:00 barra, 13:00-14:00 enlace, 14:00-15:00 barra]
    no puede formarse completa porque falta skill para la demanda central.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-barra"})  # solo barra, sin enlace

    dms = [
        MockDemand("d1", DAY, "ws-barra", time(12, 0), time(13, 0)),
        MockDemand("d2", DAY, "ws-enlace", time(13, 0), time(14, 0)),
        MockDemand("d3", DAY, "ws-barra", time(14, 0), time(15, 0)),
    ]
    sched = defaultdict(list)
    estados = {"A": _empty_estado("A")}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    _, _, s, _, _ = gen._short_block_recovery_pass([emp], dms, sched, estados, cov, remaining, set())

    # d1 y d3 no son contiguas (hay un gap) → ninguna cadena >= 3h posible
    assert s == 0, "Sin skill en una demanda intermedia la cadena se rompe y no alcanza 3h"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 5: Prioriza empleado sin asignación ese día
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_prioritizes_employee_without_assignment_today():
    """
    Hay dos empleados: A (sin asignación hoy) y B (ya tiene 4h hoy).
    Ambos pueden cubrir la cadena de 3 demandas × 1h.
    El empleado A debe ser el elegido (mayor prioridad por score).
    """
    gen = _make_gen()
    emp_a = MockEmp("A", {"ws-barra"})  # sin asignación
    emp_b = MockEmp("B", {"ws-barra"})  # ya tiene 4h

    dms = [
        MockDemand("d1", DAY, "ws-barra", time(15, 0), time(16, 0)),
        MockDemand("d2", DAY, "ws-barra", time(16, 0), time(17, 0)),
        MockDemand("d3", DAY, "ws-barra", time(17, 0), time(18, 0)),
    ]
    # Estado de B: ya tiene 4h hoy (08:00-12:00, bloque válido)
    estado_b = _empty_estado("B")
    estado_b.registrar(DAY, "ws-barra", 8 * 60, 12 * 60)

    sched = defaultdict(list)
    # Las 4h de B ya están en el horario (bloque válido previo)
    dummy_dm = MockDemand("d_prev", DAY, "ws-barra", time(8, 0), time(12, 0))
    sched[DAY].append((emp_b, dummy_dm))

    estados = {"A": _empty_estado("A"), "B": estado_b}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    _, _, s, _, _ = gen._short_block_recovery_pass([emp_a, emp_b], dms, sched, estados, cov, remaining, set())

    assert s == 3, f"Deben asignarse 3 slots, got {s}"

    # Verificar que las demandas fueron asignadas a emp_a (prioridad por ser nuevo)
    assigned_emps_for_new_demands = {str(e.id) for e, dm in sched[DAY] if dm.id in {"d1", "d2", "d3"}}
    assert "A" in assigned_emps_for_new_demands, "El empleado A (sin asignación hoy) debe haber recibido la cadena"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 6: No deja bloques finales < 3h
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_does_not_create_short_blocks():
    """
    Tras ShortBlockRecoveryPass, ningún bloque continuo en el horario debe
    ser < 3h. Escenario: demanda de 2h no cubierta (sin cadena válida) y
    demanda de 3h sí cubierta → el 2h no se añade, el 3h sí.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-barra"})

    dm_short_chain = MockDemand(
        "d_short", DAY, "ws-barra", time(15, 0), time(16, 0)
    )  # solo 1h, sin par → cadena < 3h → rechazada
    dm_long_chain_1 = MockDemand("d_long1", DAY, "ws-barra", time(18, 0), time(19, 0))
    dm_long_chain_2 = MockDemand("d_long2", DAY, "ws-barra", time(19, 0), time(20, 0))
    dm_long_chain_3 = MockDemand("d_long3", DAY, "ws-barra", time(20, 0), time(21, 0))

    dms = [dm_short_chain, dm_long_chain_1, dm_long_chain_2, dm_long_chain_3]
    sched = defaultdict(list)
    estados = {"A": _empty_estado("A")}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    gen._short_block_recovery_pass([emp], dms, sched, estados, cov, remaining, set())

    # Verificar que ningún bloque en el horario es < 3h
    blocks = gen._get_contiguous_blocks_for_employee_day(sched.get(DAY, []))
    for blk in blocks:
        assert blk["duration_min"] >= MIN_BLK_MIN, (
            f"Bloque < 3h encontrado: {blk['duration_min']/60:.1f}h en "
            f"{blk['start_min']//60:02d}:{blk['start_min']%60:02d}-"
            f"{blk['end_min']//60:02d}:{blk['end_min']%60:02d}"
        )


# ─────────────────────────────────────────────────────────────────────────────
# TEST 7: Mejora cobertura sin violaciones duras
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_improves_coverage_without_hard_violations():
    """
    Hay 3 demandas no cubiertas que forman una cadena de 3h.
    Después del pase: covered aumenta de 0 a 3 y ninguna regla dura se viola.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-barra"}, weekly_minutes=40 * 60)

    dms = [
        MockDemand("d1", DAY, "ws-barra", time(9, 0), time(10, 0)),
        MockDemand("d2", DAY, "ws-barra", time(10, 0), time(11, 0)),
        MockDemand("d3", DAY, "ws-barra", time(11, 0), time(12, 0)),
    ]
    sched = defaultdict(list)
    estados = {"A": _empty_estado("A")}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    prev_covered = sum(c["covered"] for c in cov.values())
    gen._short_block_recovery_pass([emp], dms, sched, estados, cov, remaining, set())
    post_covered = sum(c["covered"] for c in cov.values())

    assert post_covered > prev_covered, "La cobertura debe aumentar"
    assert post_covered - prev_covered == 3

    # Verificar límites diarios / semanales
    estado = estados["A"]
    max_h_min = gen.reglas.get("max_horas_por_dia", 9) * 60
    assert estado.minutos_por_dia.get(DAY, 0) <= max_h_min, "No debe superar max_horas_dia"
    limit_weekly = gen.reglas.get("max_horas_por_dia", 9) * 60 * 7
    assert estado.minutos_semana <= limit_weekly, "No debe superar límite semanal"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 8: No muta horario si no hay cadenas válidas
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_no_mutation_when_no_valid_chains():
    """
    Si todas las demandas son 1h aisladas (no contiguas entre sí) y solo hay
    un empleado, no se puede formar ninguna cadena >= 3h.
    El horario, estados, cov y remaining deben quedar exactamente igual.
    """
    gen = _make_gen()
    emp = MockEmp("A", {"ws-barra"})

    # Demandas con gaps entre ellas (no contiguas)
    dms = [
        MockDemand("d1", DAY, "ws-barra", time(9, 0), time(10, 0)),  # 1h
        MockDemand("d2", DAY, "ws-barra", time(12, 0), time(13, 0)),  # 1h — gap de 2h
        MockDemand("d3", DAY, "ws-barra", time(15, 0), time(16, 0)),  # 1h — gap de 2h
    ]
    sched = defaultdict(list)
    estados = {"A": _empty_estado("A")}
    cov = _make_cov(dms)
    remaining = _make_remaining(dms)

    snap_remaining = dict(remaining)
    snap_covered = {k: v["covered"] for k, v in cov.items()}

    _, _, s, _, _ = gen._short_block_recovery_pass([emp], dms, sched, estados, cov, remaining, set())

    assert s == 0, "No deben agregarse slots si no hay cadenas válidas"
    assert dict(remaining) == snap_remaining, "remaining no debe cambiar"
    assert {k: v["covered"] for k, v in cov.items()} == snap_covered
    assert len(sched[DAY]) == 0


# ─────────────────────────────────────────────────────────────────────────────
# TEST 9: _validate_chain_for_employee cubre todas las reglas duras
# ─────────────────────────────────────────────────────────────────────────────


def test_validate_chain_covers_hard_rules():
    """
    Valida que _validate_chain_for_employee retorna (False, reason) correcta
    para distintas violaciones duras:
      a) Sin skill           → SIN_SKILL
      b) MAX_HORAS_DIA       → MAX_HORAS_DIA
      c) Bloque < 3h (cadena sola de 1h, sin existentes)  → BLOQUE_CORTO_FINAL
      d) Cadena válida 3h    → (True, "")
    """
    gen = _make_gen()

    # (a) Sin skill
    emp_no_skill = MockEmp("X", {"ws-otro"})
    estado = _empty_estado("X")
    chain_1h = [MockDemand("dx", DAY, "ws-barra", time(12, 0), time(13, 0))]
    ok, reason = gen._validate_chain_for_employee(emp_no_skill, chain_1h, DAY, estado, set(), MIN_BLK_MIN)
    assert not ok and reason == "SIN_SKILL"

    # (b) MAX_HORAS_DIA: empleado ya tiene 9h ese día
    emp_full = MockEmp("Y", {"ws-barra"})
    estado_full = _empty_estado("Y")
    estado_full.registrar(DAY, "ws-barra", 8 * 60, 17 * 60)  # 9h exactas
    chain_extra = [MockDemand("dy", DAY, "ws-barra", time(17, 0), time(18, 0))]
    ok, reason = gen._validate_chain_for_employee(emp_full, chain_extra, DAY, estado_full, set(), MIN_BLK_MIN)
    assert not ok and reason == "MAX_HORAS_DIA", f"got reason={reason}"

    # (c) Bloque resultante < 3h (cadena de 1h, sin existentes)
    emp_c = MockEmp("Z", {"ws-barra"})
    estado_c = _empty_estado("Z")
    chain_short = [MockDemand("dz", DAY, "ws-barra", time(12, 0), time(13, 0))]
    ok, reason = gen._validate_chain_for_employee(emp_c, chain_short, DAY, estado_c, set(), MIN_BLK_MIN)
    assert not ok and reason == "BLOQUE_CORTO_FINAL", f"got reason={reason}"

    # (d) Cadena válida de exactamente 3h (3 × 1h contiguas)
    emp_d = MockEmp("W", {"ws-barra"})
    estado_d = _empty_estado("W")
    chain_3h = [
        MockDemand("dw1", DAY, "ws-barra", time(12, 0), time(13, 0)),
        MockDemand("dw2", DAY, "ws-barra", time(13, 0), time(14, 0)),
        MockDemand("dw3", DAY, "ws-barra", time(14, 0), time(15, 0)),
    ]
    ok, reason = gen._validate_chain_for_employee(emp_d, chain_3h, DAY, estado_d, set(), MIN_BLK_MIN)
    assert ok, f"Cadena de 3h debe ser válida, got reason={reason}"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 10: generar() con SBR produce final_short_blocks = 0
# ─────────────────────────────────────────────────────────────────────────────


def test_sbr_full_generar_has_zero_short_blocks():
    """
    Integración completa. generar() con ShortBlockRecoveryPass activo debe
    producir un horario donde NINGÚN bloque continuo es < 3h.
    Incluye demandas cortas (1h) contiguas que solo juntas forman 3h.
    """
    gen = _make_gen()
    week = [DAY + datetime.timedelta(days=i) for i in range(7)]

    emp = MockEmp("A", {"ws-barra", "ws-comedor"}, weekly_minutes=40 * 60)

    demands = [
        # Lunes: 3 × 1h = bloque 3h candidato para SBR
        MockDemand("m1", week[0], "ws-barra", time(10, 0), time(11, 0)),
        MockDemand("m2", week[0], "ws-barra", time(11, 0), time(12, 0)),
        MockDemand("m3", week[0], "ws-barra", time(12, 0), time(13, 0)),
        # Martes: 1 demanda larga de 4h (normalmente cubierta por FASE 1)
        MockDemand("t1", week[1], "ws-comedor", time(14, 0), time(18, 0)),
    ]

    sched, coverage_stats, _ = gen.generar([emp], demands, week)

    # Ningún bloque < 3h en el horario final
    violations = []
    for d, assignments in sched.items():
        by_emp = defaultdict(list)
        for e, dm in assignments:
            if dm.wsid is not None:
                by_emp[str(e.id)].append((e, dm))
        for eid, pairs in by_emp.items():
            for blk in gen._get_contiguous_blocks_for_employee_day(pairs):
                if blk["duration_min"] < MIN_BLK_MIN:
                    violations.append(
                        f"emp={eid} {d} "
                        f"{blk['start_min']//60:02d}:{blk['start_min']%60:02d}-"
                        f"{blk['end_min']//60:02d}:{blk['end_min']%60:02d} "
                        f"= {blk['duration_min']/60:.1f}h"
                    )

    assert violations == [], f"El horario final contiene {len(violations)} bloques < 3h:\n" + "\n".join(violations)
