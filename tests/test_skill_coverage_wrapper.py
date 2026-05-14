# tests/test_skill_coverage_wrapper.py
"""
Tests de integración para apply_skill_coverage_analysis_if_available() de agenda.py.

Validan que el wrapper:
  1. Agrega skill_coverage_report a la respuesta cuando el analyzer funciona.
  2. No rompe generate_ai si el analyzer lanza una excepción.
  3. No muta sched ni coverage_stats.
  4. Ignora demandas con wsid=None (pseudo-demandas de ausencia).
  5. El reporte retornado es JSON-serializable.
  6. El log [SKILL-COVERAGE] contiene los campos de resumen requeridos.
  7. Retorna dict vacío (solo "_log") cuando el analyzer falla.
  8. El reporte contiene las 8 secciones esperadas.

Los tests NO usan base de datos ni Flask.  Importan el wrapper directamente
desde agenda.py usando el mismo patrón de aislamiento que test_repair_wrapper.py.
"""

from __future__ import annotations

import copy
import json
import sys
import types
from collections import defaultdict
from datetime import date, time
from typing import Any, Dict, List
from unittest.mock import MagicMock, patch

import pytest

# ─────────────────────────────────────────────────────────────────────────────
# IMPORTACIÓN AISLADA DEL WRAPPER (sin Flask / psycopg2 / BD)
# ─────────────────────────────────────────────────────────────────────────────


def _import_agenda_module():
    """
    Carga agenda.py inyectando mocks de los módulos pesados.
    Reutiliza el módulo si ya está en sys.modules.
    """
    _heavy = ["psycopg2", "psycopg2.extensions", "flask", "flask_cors"]
    _injected = []
    for mod in _heavy:
        if mod not in sys.modules:
            sys.modules[mod] = MagicMock()
            _injected.append(mod)

    try:
        if "agenda" in sys.modules:
            return sys.modules["agenda"]

        import importlib.util, pathlib

        spec = importlib.util.spec_from_file_location(
            "agenda",
            str(pathlib.Path(__file__).parents[1] / "agenda.py"),
        )
        mod = importlib.util.module_from_spec(spec)
        sys.modules["agenda"] = mod
        spec.loader.exec_module(mod)
        return mod
    finally:
        for mod_name in _injected:
            sys.modules.pop(mod_name, None)


try:
    _agenda = _import_agenda_module()
    _apply_skill_coverage = _agenda.apply_skill_coverage_analysis_if_available
    WRAPPER_AVAILABLE = True
except Exception as _import_err:
    WRAPPER_AVAILABLE = False
    _import_err_msg = str(_import_err)

pytestmark = pytest.mark.skipif(
    not WRAPPER_AVAILABLE,
    reason=f"No se pudo importar agenda.py: {_import_err_msg if not WRAPPER_AVAILABLE else ''}",
)

# ─────────────────────────────────────────────────────────────────────────────
# STUBS MÍNIMOS
# ─────────────────────────────────────────────────────────────────────────────

MONDAY = date(2026, 5, 18)
WS_BARRA = "ws-barra"
WS_COCINA = "ws-cocina"


class _Emp:
    """Empleado stub compatible con SkillCoverageAnalyzer (duck-typing)."""

    def __init__(self, emp_id: str, roles: set, weekly_minutes: int = 40 * 60):
        self.id = emp_id
        self.name = f"Emp-{emp_id}"
        self.roles = roles
        self.day_off: set = set()
        self.absent: set = set()
        self.hired_hours = weekly_minutes / 60.0
        self._wlimit = weekly_minutes

    def can(self, ws_id: str) -> bool:
        return str(ws_id) in {str(r) for r in self.roles}

    def off(self, d) -> bool:
        return False

    def absent_day(self, d) -> bool:
        return False

    def available(self, d, s, e) -> bool:
        return True

    def weekly_hours_limit(self) -> int:
        return self._wlimit


class _Demand:
    """Demanda stub con todos los campos que espera SkillCoverageAnalyzer."""

    _counter = 0

    def __init__(self, dm_id: str, d: date, ws_id, ws_name: str, start: time, end: time, need: int = 1):
        self.id = dm_id
        self.date = d
        self.wsid = ws_id
        self.wsname = ws_name
        self.start = start
        self.end = end
        self.need = need
        self.raw_need = float(need)
        self.has_hybrid_component = False
        self.observation_override = None
        self.user_shift_windows = {}
        self.hybrid_group_id = None
        self.shift_type = None
        self.slot_index = 0


def _cs(dm: _Demand, covered: int) -> dict:
    """Crea una entrada estándar de coverage_stats."""
    unmet = max(0, dm.need - covered)
    pct = round((covered / dm.need) * 100, 1) if dm.need else 100.0
    return {
        "demand": dm,
        "covered": covered,
        "unmet": unmet,
        "met": covered,
        "coverage_pct": pct,
        "employees": [],
    }


# ─────────────────────────────────────────────────────────────────────────────
# FIXTURES
# ─────────────────────────────────────────────────────────────────────────────


@pytest.fixture
def fully_covered_setup():
    """Horario con 100% de cobertura → el analyzer no genera huecos."""
    emp = _Emp("A", {WS_BARRA})
    dm = _Demand("dm1", MONDAY, WS_BARRA, "Barra", time(9, 0), time(13, 0))
    sched = defaultdict(list, {MONDAY: [(emp, dm)]})
    coverage_stats = {"dm1": _cs(dm, 1)}
    return [emp], [dm], sched, coverage_stats


@pytest.fixture
def gap_setup():
    """Horario con un hueco: WS_COCINA sin personal calificado (STRUCTURAL_NO_SKILL)."""
    emp_barra = _Emp("A", {WS_BARRA})
    dm_barra = _Demand("dm-barra", MONDAY, WS_BARRA, "Barra", time(9, 0), time(13, 0))
    dm_cocina = _Demand("dm-cocina", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0))
    sched = defaultdict(list, {MONDAY: [(emp_barra, dm_barra)]})
    coverage_stats = {
        "dm-barra": _cs(dm_barra, 1),
        "dm-cocina": _cs(dm_cocina, 0),  # no cubierto
    }
    return [emp_barra], [dm_barra, dm_cocina], sched, coverage_stats


# ─────────────────────────────────────────────────────────────────────────────
# TEST 1 — El reporte se agrega a la respuesta cuando el analyzer funciona
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_report_added_to_response(gap_setup):
    emps, demands, sched, cs = gap_setup
    report = _apply_skill_coverage(emps, demands, sched, cs)

    assert isinstance(report, dict)
    # El reporte no debe estar vacío cuando hay huecos
    assert len(report) > 0
    # Debe contener el log interno
    assert "_log" in report
    assert report["_log"]["enabled"] is True
    assert report["_log"]["failed"] is False


# ─────────────────────────────────────────────────────────────────────────────
# TEST 2 — El wrapper no rompe si el analyzer lanza una excepción
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_failure_does_not_break_generate_ai(gap_setup):
    emps, demands, sched, cs = gap_setup

    with patch(
        "services.skill_coverage_analyzer.SkillCoverageAnalyzer.analyze",
        side_effect=RuntimeError("boom"),
    ):
        report = _apply_skill_coverage(emps, demands, sched, cs)

    # El wrapper debe devolver sin propagar la excepción
    assert isinstance(report, dict)
    log = report.get("_log", {})
    assert log.get("failed") is True
    assert "RuntimeError" in log.get("error", "")


# ─────────────────────────────────────────────────────────────────────────────
# TEST 3 — No muta sched ni coverage_stats
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_does_not_mutate_schedule(gap_setup):
    emps, demands, sched, cs = gap_setup

    # Capturas profundas antes de llamar al wrapper
    sched_before = {d: list(lst) for d, lst in sched.items()}
    cs_before = {k: dict(v) for k, v in cs.items()}

    _apply_skill_coverage(emps, demands, sched, cs)

    # Verificar que sched no fue modificado
    assert set(sched.keys()) == set(sched_before.keys())
    for d, lst in sched_before.items():
        assert sched[d] == lst, f"sched mutado en fecha {d}"

    # Verificar que coverage_stats no fue modificado
    assert set(cs.keys()) == set(cs_before.keys())
    for k, v in cs_before.items():
        assert cs[k]["covered"] == v["covered"], f"cs mutado en {k}: covered"
        assert cs[k]["unmet"] == v["unmet"], f"cs mutado en {k}: unmet"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 4 — Ignora demandas con wsid=None (pseudo-demandas de ausencia)
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_ignores_wsid_none_demands():
    """
    Las pseudo-demandas de ausencia tienen wsid=None.
    El wrapper las filtra antes de llamar al analyzer.
    """
    emp = _Emp("A", {WS_BARRA})
    dm_real = _Demand("dm-real", MONDAY, WS_BARRA, "Barra", time(9, 0), time(13, 0))
    # Simula pseudo-demanda de ausencia (wsid=None)
    dm_abs = _Demand("dm-abs", MONDAY, None, "AUSENCIA", time(0, 0), time(0, 0))
    dm_abs.wsid = None

    sched = defaultdict(list, {MONDAY: [(emp, dm_real), (emp, dm_abs)]})
    coverage_stats = {
        "dm-real": _cs(dm_real, 1),
        # dm-abs no está en coverage_stats (no es demanda real)
    }

    # Si el analyzer recibiera dm_abs, wsid=None causaría comportamiento inesperado.
    # Verificamos que no falla (el filtro funciona).
    report = _apply_skill_coverage([emp], [dm_real, dm_abs], sched, coverage_stats)

    assert isinstance(report, dict)
    log = report.get("_log", {})
    # 100% cobertura (dm_real cubierto), no debe haber error
    assert log.get("failed") is False


# ─────────────────────────────────────────────────────────────────────────────
# TEST 5 — El reporte es JSON-serializable
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_report_is_json_serializable(gap_setup):
    emps, demands, sched, cs = gap_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)

    # No debe lanzar TypeError/ValueError
    try:
        serialized = json.dumps(report)
    except (TypeError, ValueError) as exc:
        pytest.fail(f"El reporte no es JSON-serializable: {exc}")

    # El JSON round-trip debe ser un dict válido
    recovered = json.loads(serialized)
    assert isinstance(recovered, dict)


# ─────────────────────────────────────────────────────────────────────────────
# TEST 6 — El log contiene los campos de resumen requeridos
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_log_contains_summary(gap_setup):
    emps, demands, sched, cs = gap_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)
    log = report.get("_log", {})

    required_fields = {
        "enabled",
        "workstations",
        "structural",
        "algorithmic",
        "critical",
        "recommendations",
        "time_ms",
        "failed",
        "error",
    }
    missing = required_fields - set(log.keys())
    assert not missing, f"Campos faltantes en _log: {missing}"

    # Tipos básicos
    assert isinstance(log["enabled"], bool)
    assert isinstance(log["workstations"], int)
    assert isinstance(log["structural"], int)
    assert isinstance(log["algorithmic"], int)
    assert isinstance(log["critical"], int)
    assert isinstance(log["recommendations"], int)
    assert isinstance(log["time_ms"], (int, float))
    assert isinstance(log["failed"], bool)
    assert isinstance(log["error"], str)


# ─────────────────────────────────────────────────────────────────────────────
# TEST 7 — Retorna dict con solo "_log" cuando el analyzer falla
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_returns_empty_on_failure(gap_setup):
    emps, demands, sched, cs = gap_setup

    with patch(
        "services.skill_coverage_analyzer.SkillCoverageAnalyzer.analyze",
        side_effect=ValueError("error de prueba"),
    ):
        report = _apply_skill_coverage(emps, demands, sched, cs)

    # Solo debe contener "_log"
    assert set(report.keys()) == {"_log"}
    assert report["_log"]["failed"] is True
    assert "ValueError" in report["_log"]["error"]


# ─────────────────────────────────────────────────────────────────────────────
# TEST 8 — El reporte contiene las 8 secciones esperadas
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_report_contains_8_sections(gap_setup):
    emps, demands, sched, cs = gap_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)

    # El reporte exitoso debe tener las 8 secciones de to_report_dict()
    expected_sections = {
        "global_summary",
        "workstations_ranking",
        "top_deficit_causes",
        "structural_gaps",
        "algorithmic_gaps",
        "training_recommendations",
        "hiring_recommendations",
        "recurrent_patterns",
    }

    log = report.get("_log", {})
    if log.get("failed"):
        pytest.skip("El analyzer falló — no hay secciones que validar")

    missing = expected_sections - set(report.keys())
    assert not missing, f"Secciones faltantes en el reporte: {missing}"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 9 — Cobertura completa → workstations=0 (sin huecos)
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_zero_workstations_when_fully_covered(fully_covered_setup):
    emps, demands, sched, cs = fully_covered_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)

    log = report.get("_log", {})
    assert log.get("failed") is False
    # Sin huecos → el analyzer devuelve lista vacía → workstations=0
    assert log.get("workstations", -1) == 0


# ─────────────────────────────────────────────────────────────────────────────
# TEST 10 — structural > 0 cuando hay pool=0 para algún ws
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_structural_count_when_no_qualified_employee(gap_setup):
    """
    gap_setup tiene WS_COCINA sin ningún empleado calificado.
    El log debe reportar al menos structural=1.
    """
    emps, demands, sched, cs = gap_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)
    log = report.get("_log", {})

    assert log.get("failed") is False
    assert log.get("structural", 0) >= 1


# ─────────────────────────────────────────────────────────────────────────────
# TEST 11 — critical > 0 cuando hay ws con pool=0 (STRUCTURAL_NO_SKILL → CRITICAL)
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_critical_when_pool_is_zero(gap_setup):
    emps, demands, sched, cs = gap_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)
    log = report.get("_log", {})

    assert log.get("failed") is False
    assert log.get("critical", 0) >= 1


# ─────────────────────────────────────────────────────────────────────────────
# TEST 12 — Tiempo de ejecución registrado en milisegundos
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_time_ms_is_non_negative(gap_setup):
    emps, demands, sched, cs = gap_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)
    log = report.get("_log", {})

    assert log["time_ms"] >= 0


# ─────────────────────────────────────────────────────────────────────────────
# TEST 13 — El reporte no contiene objetos Emp ni Demand directamente
# ─────────────────────────────────────────────────────────────────────────────


def test_skill_coverage_report_contains_no_raw_objects(gap_setup):
    """
    El reporte debe contener solo tipos primitivos serializables.
    No deben haber instancias de _Emp, _Demand ni de dataclasses del analyzer.
    """
    emps, demands, sched, cs = gap_setup

    report = _apply_skill_coverage(emps, demands, sched, cs)
    log = report.get("_log", {})
    if log.get("failed"):
        pytest.skip("El analyzer falló")

    # Si json.dumps funciona (test 5), no hay objetos crudos.
    # Verificación adicional: ningún valor de primer nivel es un objeto custom.
    PRIMITIVE_TYPES = (str, int, float, bool, list, dict, type(None))
    for key, val in report.items():
        assert isinstance(val, PRIMITIVE_TYPES), f"Clave '{key}' contiene tipo no primitivo: {type(val).__name__}"
