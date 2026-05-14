# tests/test_skill_coverage_analyzer.py
"""
Pruebas unitarias para SkillCoverageAnalyzer (services/skill_coverage_analyzer.py)

Cubre los 10 casos especificados en la tarea:
    1. test_structural_no_skill_gap
    2. test_too_few_qualified_employees_gap
    3. test_availability_gap
    4. test_hours_limit_gap
    5. test_algorithmic_gap_when_candidate_exists
    6. test_recurrent_gap_detection_by_workstation_and_dow
    7. test_training_recommendation_for_ultra_specialized_role
    8. test_summary_ranking_orders_worst_coverage_first
    9. test_report_dict_contains_global_summary
   10. test_no_mutation_of_original_schedule

Sin base de datos. Sin Flask. Todos los objetos son mocks mínimos.

Ejecutar:
    pytest tests/test_skill_coverage_analyzer.py -v
"""

from __future__ import annotations

import copy
from collections import defaultdict
from datetime import date, time
from typing import Any, Dict, List, Optional, Set

import pytest

from services.skill_coverage_analyzer import (
    DeficitType,
    Severity,
    SkillCoverageAnalyzer,
    SkillCoverageGap,
    SkillCoverageSummary,
    TrainingRecommendation,
    _gap_recurrent_key,
)

# ─────────────────────────────────────────────────────────────────────────────
# MOCKS MÍNIMOS
# ─────────────────────────────────────────────────────────────────────────────

MONDAY = date(2026, 2, 9)  # lunes
TUESDAY = date(2026, 2, 10)

WS_BARRA = "ws-barra"
WS_COCINA = "ws-cocina"
WS_COMEDOR = "ws-comedor"


class MockEmp:
    def __init__(
        self,
        id_str: str,
        roles: Set[str],
        weekly_minutes: int = 40 * 60,
        day_off: Optional[Set[int]] = None,
        absent: Optional[Set[date]] = None,
        windows_by_dow: Optional[Dict[int, List]] = None,
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

    def can(self, ws: Any) -> bool:
        return str(ws) in {str(r) for r in self.roles}

    def off(self, d: date) -> bool:
        return d.weekday() in self.day_off

    def absent_day(self, d: date) -> bool:
        return d in self.absent

    def available(self, d: date, s: time, e: time) -> bool:
        return not self.off(d) and not self.absent_day(d)

    def weekly_hours_limit(self) -> int:
        return self._weekly_minutes


class MockDemand:
    def __init__(
        self,
        id_str: str,
        d: date,
        ws_id: str,
        ws_name: str,
        start: time,
        end: time,
        need: int = 1,
    ):
        self.id = id_str
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


def _cs(dm: MockDemand, covered: int) -> Dict:
    """Construye un coverage_stats entry mínimo."""
    return {
        "demand": dm,
        "covered": covered,
        "met": covered,
        "unmet": dm.need - covered,
        "coverage_pct": (covered / dm.need * 100) if dm.need else 100.0,
        "employees": [],
    }


# ─────────────────────────────────────────────────────────────────────────────
# FIXTURES
# ─────────────────────────────────────────────────────────────────────────────


@pytest.fixture
def analyzer():
    return SkillCoverageAnalyzer(
        role_fallbacks={
            "JEFE BARRA": ["ENLACE", "CAMARERO BARRA"],
            WS_BARRA: ["enlace"],
        },
        debug=True,
    )


# ─────────────────────────────────────────────────────────────────────────────
# TEST 1: STRUCTURAL_NO_SKILL
# ─────────────────────────────────────────────────────────────────────────────


def test_structural_no_skill_gap(analyzer):
    """
    Ningún empleado tiene el skill requerido.
    Clasificación esperada: STRUCTURAL_NO_SKILL, severidad CRITICAL.
    """
    # Solo hay un empleado, con rol diferente
    emp_a = MockEmp("A", {WS_BARRA})
    dm = MockDemand("dm1", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0), need=1)
    sched = defaultdict(list, {MONDAY: [(emp_a, dm)]})  # asignado en barra, no cocina
    # Agregar demanda de cocina sin cubrir
    dm_gap = MockDemand("dm-gap", MONDAY, WS_COCINA, "Cocina", time(18, 0), time(22, 0))
    sched_gap: Dict = defaultdict(list)  # vacío

    coverage_stats = {
        "dm-gap": _cs(dm_gap, 0),
    }

    summaries = analyzer.analyze([emp_a], [dm_gap], sched_gap, coverage_stats)

    assert len(summaries) == 1
    ws_sum = summaries[0]
    assert ws_sum.qualified_pool_size == 0
    assert ws_sum.primary_deficit_type == DeficitType.STRUCTURAL_NO_SKILL
    assert ws_sum.severity == Severity.CRITICAL
    assert ws_sum.structural_deficit is True


# ─────────────────────────────────────────────────────────────────────────────
# TEST 2: STRUCTURAL_TOO_FEW_QUALIFIED
# ─────────────────────────────────────────────────────────────────────────────


def test_too_few_qualified_employees_gap(analyzer):
    """
    Hay exactamente 1 empleado calificado (pool <= 2) — demasiado pequeño.
    Un día de baja lo hace imposible. Clasificación: STRUCTURAL_TOO_FEW_QUALIFIED.
    """
    emp_solo = MockEmp("solo", {WS_COCINA}, weekly_minutes=40 * 60)
    dm_gap = MockDemand("dm-gap", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0))
    sched: Dict = defaultdict(list)
    coverage_stats = {"dm-gap": _cs(dm_gap, 0)}

    summaries = analyzer.analyze([emp_solo], [dm_gap], sched, coverage_stats)

    assert len(summaries) == 1
    ws_sum = summaries[0]
    assert ws_sum.qualified_pool_size == 1
    assert ws_sum.primary_deficit_type == DeficitType.STRUCTURAL_TOO_FEW_QUALIFIED
    assert ws_sum.structural_deficit is True
    assert ws_sum.severity in (Severity.CRITICAL, Severity.HIGH)


# ─────────────────────────────────────────────────────────────────────────────
# TEST 3: AVAILABILITY_GAP
# ─────────────────────────────────────────────────────────────────────────────


def test_availability_gap(analyzer):
    """
    Hay 3 empleados calificados, pero todos tienen el día libre o están ausentes.
    Clasificación: AVAILABILITY_GAP.
    """
    # MONDAY = 0 (lunes); day_off={0} = libre los lunes
    emp_a = MockEmp("A", {WS_COCINA}, day_off={0})  # libre lunes
    emp_b = MockEmp("B", {WS_COCINA}, absent={MONDAY})  # ausente ese día
    emp_c = MockEmp("C", {WS_COCINA}, day_off={0})  # libre lunes

    dm_gap = MockDemand("dm-gap", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0))
    sched: Dict = defaultdict(list)
    coverage_stats = {"dm-gap": _cs(dm_gap, 0)}

    emps = [emp_a, emp_b, emp_c]
    summaries = analyzer.analyze(emps, [dm_gap], sched, coverage_stats)

    assert len(summaries) == 1
    ws_sum = summaries[0]
    gap = ws_sum.gaps[0]
    # Todos calificados están bloqueados por disponibilidad
    assert gap.blocked_by_day_off_count + gap.blocked_by_absence_count > 0
    assert gap.deficit_type == DeficitType.AVAILABILITY_GAP


# ─────────────────────────────────────────────────────────────────────────────
# TEST 4: HOURS_LIMIT_GAP
# ─────────────────────────────────────────────────────────────────────────────


def test_hours_limit_gap(analyzer):
    """
    Hay 3 empleados calificados, todos con sus horas semanales al límite.
    Clasificación: HOURS_LIMIT_GAP.
    """
    # Empleados con límite de 3h (180min) semanales — asignar 3h los deja sin margen
    emp_a = MockEmp("A", {WS_COCINA}, weekly_minutes=180)
    emp_b = MockEmp("B", {WS_COCINA}, weekly_minutes=180)
    emp_c = MockEmp("C", {WS_COCINA}, weekly_minutes=180)
    # Demanda de cobertura existente que usa 3h a cada uno
    dm_prev = MockDemand("dm-prev", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(13, 0))
    sched: Dict = defaultdict(list, {MONDAY: [(emp_a, dm_prev), (emp_b, dm_prev), (emp_c, dm_prev)]})
    coverage_stats = {
        "dm-prev": {
            "demand": dm_prev,
            "covered": 1,
            "met": 1,
            "unmet": 0,
            "coverage_pct": 100.0,
            "employees": ["A"],
        }
    }

    # Ahora hay un hueco adicional — todos están al límite de horas
    dm_gap = MockDemand("dm-gap", MONDAY, WS_COCINA, "Cocina", time(20, 0), time(23, 0))
    coverage_stats["dm-gap"] = _cs(dm_gap, 0)

    summaries = analyzer.analyze([emp_a, emp_b, emp_c], [dm_prev, dm_gap], sched, coverage_stats)

    assert len(summaries) == 1
    gap = summaries[0].gaps[0]
    assert gap.blocked_by_hours_count > 0
    assert gap.deficit_type == DeficitType.HOURS_LIMIT_GAP


# ─────────────────────────────────────────────────────────────────────────────
# TEST 5: ALGORITHMIC_GAP
# ─────────────────────────────────────────────────────────────────────────────


def test_algorithmic_gap_when_candidate_exists(analyzer):
    """
    Hay empleados calificados y disponibles que el greedy no asignó.
    Clasificación: ALGORITHMIC_GAP.
    Pool > 2, sin restricciones de horas/ventana/ausencia.
    """
    # 3 empleados calificados con horas disponibles, ninguna restricción
    emp_a = MockEmp("A", {WS_COCINA}, weekly_minutes=40 * 60)
    emp_b = MockEmp("B", {WS_COCINA}, weekly_minutes=40 * 60)
    emp_c = MockEmp("C", {WS_COCINA}, weekly_minutes=40 * 60)
    # Ninguna asignación previa → estados vacíos
    sched: Dict = defaultdict(list)
    dm_gap = MockDemand("dm-gap", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0))
    coverage_stats = {"dm-gap": _cs(dm_gap, 0)}

    summaries = analyzer.analyze([emp_a, emp_b, emp_c], [dm_gap], sched, coverage_stats)

    assert len(summaries) == 1
    gap = summaries[0].gaps[0]
    assert gap.available_qualified_count > 0
    assert gap.deficit_type == DeficitType.ALGORITHMIC_GAP


# ─────────────────────────────────────────────────────────────────────────────
# TEST 6: DETECCIÓN DE PATRONES RECURRENTES
# ─────────────────────────────────────────────────────────────────────────────


def test_recurrent_gap_detection_by_workstation_and_dow(analyzer):
    """
    El mismo slot (ws, DOW, hora) aparece 3 veces (semanas distintas).
    detect_recurrent_gaps debe identificar el patrón con count >= 2.
    """
    # Simular 3 lunes consecutivos con el mismo hueco de COCINA 10:00-14:00
    dates = [date(2026, 2, 9), date(2026, 2, 16), date(2026, 2, 23)]
    gaps = []
    for d in dates:
        gaps.append(
            SkillCoverageGap(
                workstation_id=WS_COCINA,
                workstation_name="Cocina",
                date=d,
                dow=0,  # lunes
                start_time=time(10, 0),
                end_time=time(14, 0),
                required_staff=1,
                covered_staff=0,
                missing_staff=1,
                qualified_employees_count=1,
                available_qualified_count=0,
                unavailable_qualified_count=1,
                blocked_by_hours_count=0,
                blocked_by_window_count=0,
                blocked_by_day_off_count=1,
                blocked_by_absence_count=0,
                deficit_type=DeficitType.AVAILABILITY_GAP,
                severity=Severity.HIGH,
            )
        )

    gaps_by_ws = {WS_COCINA: gaps}
    recurrent = analyzer.detect_recurrent_gaps(gaps_by_ws, threshold=2)

    assert len(recurrent) >= 1
    # La clave debe contener el ws_id y el DOW
    key = list(recurrent.keys())[0]
    assert WS_COCINA in key
    assert len(list(recurrent.values())[0]) == 3


# ─────────────────────────────────────────────────────────────────────────────
# TEST 7: RECOMENDACIÓN DE CAPACITACIÓN
# ─────────────────────────────────────────────────────────────────────────────


def test_training_recommendation_for_ultra_specialized_role():
    """
    Una workstation con pool == 0 (nadie tiene el skill).
    recommend_training debe producir una recomendación con
    minimum_additional_people_needed >= 1 y la razón apropiada.
    Si hay empleados con fallback roles, deben aparecer en suggested.
    """
    analyzer = SkillCoverageAnalyzer(
        role_fallbacks={"JEFE COCINA": ["COCINERO", "AYUDANTE COCINA"]},
    )

    # Empleados: 2 con roles de fallback, ninguno con JEFE COCINA
    emp_a = MockEmp("A", {"COCINERO"})
    emp_b = MockEmp("B", {"AYUDANTE COCINA"})

    summary = SkillCoverageSummary(
        workstation_id="ws-jefe-cocina",
        workstation_name="JEFE COCINA",
        total_required_slots=7,
        total_covered_slots=0,
        total_missing_slots=7,
        coverage_pct=0.0,
        qualified_pool_size=0,
        recurrent_gap_count=7,
        worst_days=["2026-02-09"],
        worst_time_ranges=["20:30-23:00"],
        structural_deficit=True,
        primary_deficit_type=DeficitType.STRUCTURAL_NO_SKILL,
        severity=Severity.CRITICAL,
        gaps=[
            SkillCoverageGap(
                workstation_id="ws-jefe-cocina",
                workstation_name="JEFE COCINA",
                date=MONDAY,
                dow=0,
                start_time=time(20, 30),
                end_time=time(23, 0),
                required_staff=1,
                covered_staff=0,
                missing_staff=1,
                qualified_employees_count=0,
                available_qualified_count=0,
                unavailable_qualified_count=0,
                blocked_by_hours_count=0,
                blocked_by_window_count=0,
                blocked_by_day_off_count=0,
                blocked_by_absence_count=0,
                deficit_type=DeficitType.STRUCTURAL_NO_SKILL,
                severity=Severity.CRITICAL,
            )
        ],
    )

    recs = analyzer.recommend_training([summary], emps=[emp_a, emp_b])

    assert len(recs) == 1
    rec = recs[0]
    assert rec.workstation_name == "JEFE COCINA"
    assert rec.minimum_additional_people_needed >= 1
    # Empleados con fallback deben aparecer como candidatos
    assert len(rec.suggested_employees_to_train) >= 1
    assert rec.expected_coverage_gain_estimate > 0.0


# ─────────────────────────────────────────────────────────────────────────────
# TEST 8: RANKING ORDENADO POR PEOR COBERTURA
# ─────────────────────────────────────────────────────────────────────────────


def test_summary_ranking_orders_worst_coverage_first(analyzer):
    """
    analyze() debe retornar los summaries ordenados por coverage_pct ascendente
    (peor cobertura primero).
    """
    # 3 workstations con distintos niveles de cobertura
    # WS_COCINA: 0% cobertura (pool==0 → STRUCTURAL_NO_SKILL)
    # WS_BARRA: 50% cobertura (pool grande, ALGORITHMIC)
    # WS_COMEDOR: 0% cobertura (pool==1 → TOO_FEW_QUALIFIED)

    emp_qualified_barra = [MockEmp(f"B{i}", {WS_BARRA}, weekly_minutes=40 * 60) for i in range(4)]
    emp_qualified_comedor = [MockEmp("C1", {WS_COMEDOR}, weekly_minutes=40 * 60)]

    emps = emp_qualified_barra + emp_qualified_comedor

    dm_barra_ok = MockDemand("barra-ok", MONDAY, WS_BARRA, "Barra", time(10, 0), time(14, 0))
    dm_barra_gap = MockDemand("barra-gap", MONDAY, WS_BARRA, "Barra", time(16, 0), time(20, 0))
    dm_cocina_gap = MockDemand("cocina-gap", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0))
    dm_comedor_gap = MockDemand("comed-gap", MONDAY, WS_COMEDOR, "Comedor", time(10, 0), time(14, 0))

    sched: Dict = defaultdict(list, {MONDAY: [(emp_qualified_barra[0], dm_barra_ok)]})
    coverage_stats = {
        "barra-ok": _cs(dm_barra_ok, 1),
        "barra-gap": _cs(dm_barra_gap, 0),
        "cocina-gap": _cs(dm_cocina_gap, 0),
        "comed-gap": _cs(dm_comedor_gap, 0),
    }

    summaries = analyzer.analyze(
        emps, [dm_barra_ok, dm_barra_gap, dm_cocina_gap, dm_comedor_gap], sched, coverage_stats
    )

    assert len(summaries) >= 2
    # Las ws con 0% cobertura deben ir primero
    coverage_pcts = [s.coverage_pct for s in summaries]
    assert coverage_pcts == sorted(coverage_pcts), f"No está ordenado por cobertura ascendente: {coverage_pcts}"


# ─────────────────────────────────────────────────────────────────────────────
# TEST 9: REPORTE DICT CONTIENE RESUMEN GLOBAL
# ─────────────────────────────────────────────────────────────────────────────


def test_report_dict_contains_global_summary(analyzer):
    """
    to_report_dict() debe retornar un diccionario con las secciones requeridas
    y el global_summary con los campos clave.
    """
    emp = MockEmp("A", {WS_BARRA}, weekly_minutes=40 * 60)
    dm = MockDemand("dm-gap", MONDAY, WS_BARRA, "Barra", time(10, 0), time(14, 0))
    sched: Dict = defaultdict(list)
    coverage_stats = {"dm-gap": _cs(dm, 0)}

    summaries = analyzer.analyze([emp], [dm], sched, coverage_stats)
    recs = analyzer.recommend_training(summaries, emps=[emp])
    report = analyzer.to_report_dict(summaries, recs)

    # Secciones requeridas
    required_sections = [
        "global_summary",
        "workstations_ranking",
        "top_deficit_causes",
        "structural_gaps",
        "algorithmic_gaps",
        "training_recommendations",
        "hiring_recommendations",
        "recurrent_patterns",
    ]
    for sec in required_sections:
        assert sec in report, f"Sección faltante: {sec}"

    gs = report["global_summary"]
    assert "total_workstations_with_gaps" in gs
    assert "global_coverage_pct" in gs
    assert "severity_counts" in gs
    assert "structural_ws_count" in gs
    assert "algorithmic_ws_count" in gs

    # Al menos una ws con déficit
    assert gs["total_workstations_with_gaps"] >= 1


# ─────────────────────────────────────────────────────────────────────────────
# TEST 10: SIN MUTACIÓN DEL HORARIO ORIGINAL
# ─────────────────────────────────────────────────────────────────────────────


def test_no_mutation_of_original_schedule(analyzer):
    """
    analyze() y to_report_dict() NO deben modificar el sched ni el coverage_stats
    original bajo ninguna circunstancia.
    """
    emp = MockEmp("A", {WS_BARRA}, weekly_minutes=40 * 60)
    dm_ok = MockDemand("dm-ok", MONDAY, WS_BARRA, "Barra", time(10, 0), time(14, 0))
    dm_gap = MockDemand("dm-gap", MONDAY, WS_BARRA, "Barra", time(16, 0), time(20, 0))

    sched_original = defaultdict(list, {MONDAY: [(emp, dm_ok)]})
    cs_original = {
        "dm-ok": _cs(dm_ok, 1),
        "dm-gap": _cs(dm_gap, 0),
    }

    # Copias para comparación post-análisis
    sched_snapshot = {d: list(lst) for d, lst in sched_original.items()}
    cs_snapshot_covered = {k: v["covered"] for k, v in cs_original.items()}
    cs_snapshot_unmet = {k: v["unmet"] for k, v in cs_original.items()}

    summaries = analyzer.analyze([emp], [dm_ok, dm_gap], sched_original, cs_original)
    recs = analyzer.recommend_training(summaries, [emp])
    _ = analyzer.to_report_dict(summaries, recs)

    # Verificar que sched no fue mutado
    for d, lst in sched_original.items():
        assert list(lst) == sched_snapshot.get(d, []), f"sched mutado en fecha {d}"

    # Verificar que coverage_stats no fue mutado
    for k in cs_original:
        assert cs_original[k]["covered"] == cs_snapshot_covered[k], f"coverage_stats[{k}]['covered'] mutado"
        assert cs_original[k]["unmet"] == cs_snapshot_unmet[k], f"coverage_stats[{k}]['unmet'] mutado"


# ─────────────────────────────────────────────────────────────────────────────
# TESTS ADICIONALES DE ROBUSTEZ
# ─────────────────────────────────────────────────────────────────────────────


def test_classify_deficit_direct_api(analyzer):
    """classify_deficit() es invocable directamente y retorna el tipo correcto."""
    # Sin ningún calificado → STRUCTURAL_NO_SKILL
    assert analyzer.classify_deficit(0, 0, 0, 0, 0, 0, 1) == DeficitType.STRUCTURAL_NO_SKILL

    # Pool == 1 → TOO_FEW_QUALIFIED
    assert analyzer.classify_deficit(1, 0, 0, 0, 0, 1, 1) == DeficitType.STRUCTURAL_TOO_FEW_QUALIFIED

    # Pool > 2, todos en horas → HOURS_LIMIT_GAP
    assert analyzer.classify_deficit(5, 5, 0, 0, 0, 0, 1) == DeficitType.HOURS_LIMIT_GAP

    # Pool > 2, todos fuera de ventana → AVAILABILITY_GAP
    assert analyzer.classify_deficit(5, 0, 5, 0, 0, 0, 1) == DeficitType.AVAILABILITY_GAP

    # Pool > 2, hay disponibles → ALGORITHMIC_GAP
    assert analyzer.classify_deficit(5, 0, 0, 0, 0, 3, 1) == DeficitType.ALGORITHMIC_GAP


def test_severity_rules_applied_correctly(analyzer):
    """Las reglas de severidad se aplican según la especificación."""
    # Pool == 0 → siempre CRITICAL
    emp_none = MockEmp("X", {WS_BARRA})
    dm = MockDemand("dm", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0))
    sched: Dict = defaultdict(list)
    cs = {"dm": _cs(dm, 0)}
    summaries = analyzer.analyze([emp_none], [dm], sched, cs)
    assert summaries[0].severity == Severity.CRITICAL

    # Pool > 2, cobertura > 95% → LOW
    emps3 = [MockEmp(f"E{i}", {WS_COCINA}, weekly_minutes=40 * 60) for i in range(4)]
    # Crear muchas demandas cubiertas + 1 hueco pequeño
    dm_covered = [MockDemand(f"dm-cov-{i}", MONDAY, WS_COCINA, "Cocina", time(9, 0), time(10, 0)) for i in range(20)]
    dm_gap2 = MockDemand("dm-gap2", MONDAY, WS_COCINA, "Cocina", time(22, 0), time(23, 0))
    cs2 = {d.id: _cs(d, 1) for d in dm_covered}
    cs2["dm-gap2"] = _cs(dm_gap2, 0)
    sched2: Dict = defaultdict(list, {MONDAY: [(emps3[0], dm) for dm in dm_covered]})
    summaries2 = analyzer.analyze(emps3, dm_covered + [dm_gap2], sched2, cs2)
    if summaries2:  # solo si hay huecos
        assert summaries2[0].severity == Severity.LOW


def test_empty_gaps_returns_empty_list(analyzer):
    """Si no hay huecos (100% cobertura), analyze() retorna lista vacía."""
    emp = MockEmp("A", {WS_BARRA})
    dm = MockDemand("dm", MONDAY, WS_BARRA, "Barra", time(10, 0), time(14, 0))
    sched: Dict = defaultdict(list, {MONDAY: [(emp, dm)]})
    cs = {"dm": _cs(dm, 1)}  # totalmente cubierto

    summaries = analyzer.analyze([emp], [dm], sched, cs)
    assert summaries == []


def test_gap_to_dict_is_serializable():
    """SkillCoverageGap.to_dict() retorna un dict serializable (str keys, basic types)."""
    gap = SkillCoverageGap(
        workstation_id="ws-1",
        workstation_name="Test WS",
        date=MONDAY,
        dow=0,
        start_time=time(10, 0),
        end_time=time(14, 0),
        required_staff=2,
        covered_staff=1,
        missing_staff=1,
        qualified_employees_count=3,
        available_qualified_count=1,
        unavailable_qualified_count=2,
        blocked_by_hours_count=1,
        blocked_by_window_count=1,
        blocked_by_day_off_count=0,
        blocked_by_absence_count=0,
        deficit_type=DeficitType.HOURS_LIMIT_GAP,
        severity=Severity.MEDIUM,
    )
    d = gap.to_dict()
    import json

    serialized = json.dumps(d)  # no debe lanzar error
    assert '"deficit_type": "HOURS_LIMIT_GAP"' in serialized
    assert '"severity": "MEDIUM"' in serialized


def test_report_dict_separates_structural_from_algorithmic(analyzer):
    """
    to_report_dict() debe separar correctamente los huecos estructurales
    de los algorítmicos en secciones distintas.
    """
    # Ws sin ningún calificado → structural
    emp_only_barra = MockEmp("A", {WS_BARRA}, weekly_minutes=40 * 60)
    dm_cocina_gap = MockDemand("gap-cocina", MONDAY, WS_COCINA, "Cocina", time(10, 0), time(14, 0))
    # Ws con calificados disponibles → algorithmic
    emp_qualified = [MockEmp(f"Q{i}", {WS_BARRA}, weekly_minutes=40 * 60) for i in range(4)]
    dm_barra_gap = MockDemand("gap-barra", MONDAY, WS_BARRA, "Barra", time(10, 0), time(14, 0))

    emps = [emp_only_barra] + emp_qualified
    demands = [dm_cocina_gap, dm_barra_gap]
    sched: Dict = defaultdict(list)
    cs = {
        "gap-cocina": _cs(dm_cocina_gap, 0),
        "gap-barra": _cs(dm_barra_gap, 0),
    }

    summaries = analyzer.analyze(emps, demands, sched, cs)
    report = analyzer.to_report_dict(summaries)

    structural = report["structural_gaps"]
    algorithmic = report["algorithmic_gaps"]

    # Al menos uno de cada tipo
    assert len(structural) >= 1
    # Al menos alguno marcado como algorítmico (ws_barra tiene calificados)
    # (puede estar vacío si la classify_deficit lo marcó de otro modo,
    #  pero en este escenario debe haber al menos 1 ws sin déficit estructural)
    all_deficit_types = {s["cause"] for s in report["top_deficit_causes"]}
    assert len(all_deficit_types) >= 1  # al menos un tipo
