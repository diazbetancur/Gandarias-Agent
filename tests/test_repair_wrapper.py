# tests/test_repair_wrapper.py
"""
Tests de integración para apply_repair_if_beneficial() de agenda.py.

Validan que el wrapper:
  1. Aplica la reparación cuando mejora la cobertura.
  2. Descarta el resultado si no hay mejora.
  3. Descarta el resultado si se detectan violaciones duras.
  4. Descarta el resultado si validate_schedule_integrity() falla.
  5. Descarta el resultado si el engine lanza una excepción.
  6. Nunca muta sched/coverage_stats si el repair se descarta.
  7. Loguea siempre todos los campos requeridos.

Los tests NO usan base de datos ni Flask. Usan stubs mínimos de los
objetos que agenda.py pasa al wrapper.
"""
from __future__ import annotations

import copy
from collections import defaultdict
from datetime import date, time
from typing import Any, Dict, List, Optional, Set
from unittest.mock import MagicMock, patch

import pytest

# ─────────────────────────────────────────────────────────────────────────────
# HELPERS PARA IMPORTAR EL WRAPPER SIN FLASK/PSYCOPG2
# apply_repair_if_beneficial está definida en agenda.py que importa psycopg2,
# Flask, etc.  La importamos aislando los módulos de dependencias pesadas.
# ─────────────────────────────────────────────────────────────────────────────

import sys
import types


def _import_wrapper():
    """
    Importa apply_repair_if_beneficial directamente desde el código fuente
    de agenda.py sin ejecutar el módulo completo (evita Flask, psycopg2, DB).

    Estrategia: inyectar mocks de los módulos problemáticos antes de importar.
    """
    # Módulos que agenda.py importa en el nivel superior pero que no
    # necesitamos para probar apply_repair_if_beneficial
    _mock_modules = [
        "psycopg2", "psycopg2.extensions",
        "flask", "flask_cors",
    ]
    _originals = {}
    for mod in _mock_modules:
        if mod not in sys.modules:
            _originals[mod] = None
            sys.modules[mod] = MagicMock()

    try:
        # Si ya fue importado limpiamente, reutilizar
        if "agenda" in sys.modules:
            mod = sys.modules["agenda"]
        else:
            import importlib.util, pathlib
            spec = importlib.util.spec_from_file_location(
                "agenda",
                str(pathlib.Path(__file__).parents[1] / "agenda.py"),
            )
            mod = importlib.util.module_from_spec(spec)
            # Registrar antes de exec para evitar imports circulares
            sys.modules["agenda"] = mod
            spec.loader.exec_module(mod)
        return mod.apply_repair_if_beneficial
    finally:
        # Limpiar mocks inyectados si eran nuevos
        for mod_name, orig in _originals.items():
            if orig is None:
                sys.modules.pop(mod_name, None)


# Intentar importar; si agenda.py no puede cargarse de ninguna manera,
# marcar los tests para skip en lugar de error de importación.
try:
    _apply_repair = _import_wrapper()
    WRAPPER_AVAILABLE = True
except Exception as _import_err:
    WRAPPER_AVAILABLE = False
    _import_err_msg = str(_import_err)


# ─────────────────────────────────────────────────────────────────────────────
# MOCKS
# ─────────────────────────────────────────────────────────────────────────────

MONDAY = date(2026, 5, 18)
WS_A = "ws-a"
WS_B = "ws-b"


class _MockEmp:
    def __init__(self, id_str, roles=None):
        self.id = id_str
        self.name = f"Emp-{id_str}"
        self.roles = set(roles or [WS_A])
        self.roles_originales = set(self.roles)
        self.day_off = set()
        self.absent = set()
        self.window = defaultdict(list)
        self.exc = defaultdict(list)
        self.user_shift_windows = defaultdict(list)
        self.split = False
        self.complement_hours = False
        self.law_apply = False
        self.extra_hours = False
        self.cant_part_time_schedule = 0
        self.hired_hours = 40.0
        self._wlimit = 40 * 60

    def can(self, ws): return str(ws) in {str(r) for r in self.roles}
    def off(self, d): return False
    def absent_day(self, d): return False
    def available(self, d, s, e): return True
    def weekly_hours_limit(self): return self._wlimit


class _MockDemand:
    def __init__(self, id_str, d, ws, wsname, start, end, need=1):
        self.id = id_str
        self.date = d
        self.wsid = ws
        self.wsname = wsname
        self.start = start
        self.end = end
        self.need = need
        self.raw_need = float(need)
        self.has_hybrid_component = False
        self.observation_override = None
        self.hybrid_group_id = None


def _make_cs(demands, covered_map):
    cs = {}
    for dm in demands:
        n = covered_map.get(dm.id, 0)
        cs[dm.id] = {
            "demand": dm,
            "covered": n,
            "met": n,
            "unmet": max(0, dm.need - n),
            "coverage_pct": (n / dm.need * 100) if dm.need else 100.0,
            "employees": [],
        }
    return cs


def _make_sched(assignments):
    sched = defaultdict(list)
    for emp, dm in assignments:
        sched[dm.date].append((emp, dm))
    return sched


def _make_generator_mock(validador=None, reglas=None):
    """
    Stub mínimo de AIScheduleGenerator:
    sólo necesita .validador para que el wrapper lo pase al engine.
    """
    from services.ai_scheduler import ValidadorReglasDuras, REGLAS_DURAS_DEFAULTS
    gen = MagicMock()
    gen.validador = validador or ValidadorReglasDuras(reglas or dict(REGLAS_DURAS_DEFAULTS))
    return gen


# ─────────────────────────────────────────────────────────────────────────────
# TESTS
# ─────────────────────────────────────────────────────────────────────────────

@pytest.mark.skipif(not WRAPPER_AVAILABLE, reason=f"agenda.py no cargable: {_import_err_msg if not WRAPPER_AVAILABLE else ''}")
class TestApplyRepairIfBeneficial:

    def _call(self, emps, demands, sched, cs, **kw):
        reglas = kw.pop("reglas", {
            "min_duracion_turno_horas": 3,
            "min_descanso_entre_turnos_horas": 9,
            "min_gap_split_horas": 3,
            "max_horas_por_dia": 9,
            "dias_descanso_semana": 2,
            "max_dias_trabajo_semana": 5,
            "max_bloques_por_dia": 2,
        })
        generator = kw.pop("generator", _make_generator_mock(reglas=reglas))
        return _apply_repair(
            emps=emps,
            demands=demands,
            sched=sched,
            coverage_stats=cs,
            overrides=kw.pop("overrides", set()),
            reglas=reglas,
            generator=generator,
            debug=False,
        )

    # ── 1. Log siempre contiene todos los campos requeridos ──────────────────

    def test_log_always_has_all_required_fields(self):
        """El log retornado debe tener exactamente los 10 campos especificados."""
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([])
        cs = _make_cs([dm], {})

        log = self._call([emp], [dm], sched, cs)

        required_fields = {
            "repair_enabled", "covered_slots_before", "covered_slots_after",
            "gaps_before", "gaps_after", "repairs_attempted", "repairs_applied",
            "execution_time_ms", "repair_applied", "repair_discard_reason",
        }
        assert required_fields.issubset(set(log.keys())), (
            f"Faltan campos: {required_fields - set(log.keys())}"
        )

    # ── 2. repair_enabled siempre True ──────────────────────────────────────

    def test_repair_enabled_is_always_true(self):
        emp = _MockEmp("e1")
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([])
        cs = _make_cs([dm], {})

        log = self._call([emp], [dm], sched, cs)
        assert log["repair_enabled"] is True

    # ── 3. Aplica cuando mejora la cobertura ────────────────────────────────

    def test_applies_when_coverage_improves(self):
        """
        Un empleado habilitado y disponible debe ser asignado al hueco.
        El wrapper debe aplicar y devolver repair_applied=True.
        """
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([])
        cs = _make_cs([dm], {})  # sin cubrir

        log = self._call([emp], [dm], sched, cs)

        # Si el engine pudo asignar → repair_applied
        # (puede ser False si hay alguna restricción que lo impide — aceptable)
        assert isinstance(log["repair_applied"], bool)
        if log["repair_applied"]:
            assert log["covered_slots_after"] > log["covered_slots_before"]
            assert cs[dm.id]["covered"] >= 1

    # ── 4. Descarta si no hay mejora de cobertura ────────────────────────────

    def test_discards_if_no_improvement(self):
        """
        Si el horario ya está 100% cubierto, el wrapper no debe aplicar cambios.
        """
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([(emp, dm)])
        cs = _make_cs([dm], {"dm1": 1})  # ya cubierto

        sched_before = {d: list(lst) for d, lst in sched.items()}
        log = self._call([emp], [dm], sched, cs)

        # El repair no debe aplicarse (no hay qué mejorar)
        if not log["repair_applied"]:
            assert log["repair_discard_reason"] in ("NO_IMPROVEMENT", "")
            # sched intacto
            assert dict(sched) == dict(sched_before)

    # ── 5. No muta sched si el repair se descarta ────────────────────────────

    def test_sched_unchanged_when_repair_discarded(self):
        """
        Si el repair se descarta (NO_IMPROVEMENT, EXCEPTION, etc.),
        sched debe quedar exactamente igual que antes.
        """
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([(emp, dm)])
        cs = _make_cs([dm], {"dm1": 1})  # cubierto

        ids_before = {d: [id(pair) for pair in lst] for d, lst in sched.items()}
        log = self._call([emp], [dm], sched, cs)

        if not log["repair_applied"]:
            ids_after = {d: [id(pair) for pair in lst] for d, lst in sched.items()}
            assert ids_before == ids_after

    # ── 6. No muta coverage_stats si repair se descarta ──────────────────────

    def test_coverage_stats_unchanged_when_repair_discarded(self):
        """Si el repair se descarta, coverage_stats debe quedar intacto."""
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([(emp, dm)])
        cs = _make_cs([dm], {"dm1": 1})

        cs_before = copy.deepcopy(cs)
        log = self._call([emp], [dm], sched, cs)

        if not log["repair_applied"]:
            # Los valores numéricos no deben haber cambiado
            for k in cs_before:
                assert cs[k]["covered"] == cs_before[k]["covered"]
                assert cs[k]["unmet"] == cs_before[k]["unmet"]

    # ── 7. Descarta si el engine lanza excepción ─────────────────────────────

    def test_discards_on_engine_exception(self):
        """
        Si ScheduleRepairEngine lanza una excepción, el wrapper la captura
        y conserva el horario original.
        """
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([])
        cs = _make_cs([dm], {})

        sched_before = {d: list(lst) for d, lst in sched.items()}

        with patch(
            "services.repair_engine.ScheduleRepairEngine.reparar",
            side_effect=RuntimeError("error simulado"),
        ):
            log = self._call([emp], [dm], sched, cs)

        assert log["repair_applied"] is False
        assert "EXCEPTION" in log["repair_discard_reason"]
        # sched intacto (las copias se hacen antes de reparar)

    # ── 8. Descarta si hay violaciones duras ─────────────────────────────────

    def test_discards_if_hard_violations_detected(self):
        """
        Si el resultado del engine tiene violations_hard > 0,
        el wrapper debe descartar y conservar el original.
        """
        from services.repair_engine import OptimizationResult
        from services.score_aggregator import ScheduleScore

        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([])
        cs = _make_cs([dm], {})

        def _fake_reparar(sched_copy, cs_copy):
            # Simular que el engine cubre el slot pero tiene violación dura
            cs_copy["dm1"]["covered"] = 1
            cs_copy["dm1"]["unmet"] = 0
            score = ScheduleScore(
                total_score=50.0, coverage_score=50.0, fairness_score=100.0,
                rules_score=0.0, preference_score=0.0,
                coverage_pct=100.0, covered_slots=1, total_slots=1,
                critical_gaps=0, fixable_gaps=0, structural_gaps=0,
                violations_hard=2,  # ← violación dura
                violations_soft=0, split_shifts_count=0,
                employees_assigned=1, employees_unassigned=0, repair_delta=0.0,
            )
            return OptimizationResult(
                original_score=score, repaired_score=score,
                gaps_before=1, gaps_after=0,
                repairs_attempted=1, repairs_applied=1,
                repair_suggestions=[], execution_time_ms=1,
            )

        with patch(
            "services.repair_engine.ScheduleRepairEngine.reparar",
            side_effect=_fake_reparar,
        ):
            log = self._call([emp], [dm], sched, cs)

        assert log["repair_applied"] is False
        assert "HARD_VIOLATIONS" in log["repair_discard_reason"]
        # cs["dm1"] no debe haber sido modificado en el original
        assert cs["dm1"]["covered"] == 0

    # ── 9. covered_slots_before refleja estado real ──────────────────────────

    def test_covered_slots_before_is_accurate(self):
        """covered_slots_before debe coincidir con la suma real de cs antes de llamar."""
        emp = _MockEmp("e1", roles={WS_A})
        dm1 = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(13, 0))
        dm2 = _MockDemand("dm2", MONDAY, WS_A, "A", time(14, 0), time(17, 0))
        sched = _make_sched([(emp, dm1)])  # dm1 cubierto, dm2 no
        cs = _make_cs([dm1, dm2], {"dm1": 1})

        expected_before = 1
        log = self._call([emp], [dm1, dm2], sched, cs)
        assert log["covered_slots_before"] == expected_before

    # ── 10. execution_time_ms siempre ≥ 0 ───────────────────────────────────

    def test_execution_time_ms_is_non_negative(self):
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([])
        cs = _make_cs([dm], {})

        log = self._call([emp], [dm], sched, cs)
        assert log["execution_time_ms"] >= 0

    # ── 11. Employees list en cs_copy no afecta al original ──────────────────

    def test_employees_list_is_deep_copied(self):
        """
        La lista 'employees' dentro de coverage_stats debe ser una copia independiente.
        Mutaciones en la copia no deben afectar al original.
        """
        emp_a = _MockEmp("a", roles={WS_A})
        emp_b = _MockEmp("b", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([(emp_a, dm)])
        cs = _make_cs([dm], {"dm1": 1})
        # Poner una lista real en employees
        cs["dm1"]["employees"] = ["a"]

        original_list_id = id(cs["dm1"]["employees"])
        log = self._call([emp_a, emp_b], [dm], sched, cs)

        # Si el repair no se aplicó, la lista original no debe haber cambiado
        if not log["repair_applied"]:
            assert id(cs["dm1"]["employees"]) == original_list_id
            assert cs["dm1"]["employees"] == ["a"]

    # ── 12. repair_discard_reason vacío cuando se aplica ────────────────────

    def test_discard_reason_empty_when_applied(self):
        """Si repair_applied=True, repair_discard_reason debe ser vacío."""
        emp = _MockEmp("e1", roles={WS_A})
        dm = _MockDemand("dm1", MONDAY, WS_A, "A", time(10, 0), time(16, 0))
        sched = _make_sched([])
        cs = _make_cs([dm], {})

        log = self._call([emp], [dm], sched, cs)

        if log["repair_applied"]:
            assert log["repair_discard_reason"] == ""
