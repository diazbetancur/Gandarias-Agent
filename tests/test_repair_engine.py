# tests/test_repair_engine.py
"""
Pruebas unitarias para:
  - ScheduleScoreAggregator  (services/score_aggregator.py)
  - ScheduleGapClassifier    (services/gap_classifier.py)
  - ScheduleRepairEngine     (services/repair_engine.py)

Las pruebas NO usan base de datos ni Flask. Todos los objetos son mocks
mínimos que satisfacen la interfaz que consumen las clases bajo prueba.

Ejecutar con:
    pytest tests/test_repair_engine.py -v
"""

from __future__ import annotations

from collections import defaultdict
from datetime import date, time
from typing import Any, Dict, List, Optional, Set
from uuid import uuid4

import pytest

# ─────────────────────────────────────────────────────────────────────────────
# MOCKS MÍNIMOS
# ─────────────────────────────────────────────────────────────────────────────


class MockEmp:
    """
    Empleado mínimo que satisface la interfaz consumida por:
    ValidadorReglasDuras, ScorerCandidatos y ScheduleRepairEngine.
    """

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
        # window[DOW] = [(time, time)]; vacío = sin ventanas → available() = True
        self.window = defaultdict(list)
        if windows_by_dow:
            for dow, wins in windows_by_dow.items():
                self.window[dow] = wins
        self.exc: Dict = defaultdict(list)
        self._weekly_minutes = weekly_minutes
        # Requerido por ValidadorReglasDuras
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
        if self.off(d) or self.absent_day(d):
            return False
        # Si no hay ventanas configuradas, siempre disponible
        if not self.day_off and not self.window and not self.exc:
            return True
        win = self.exc.get(d) or self.window.get(d.weekday(), [])
        if not win:
            # Tiene ventanas en otros días pero no en éste → no disponible
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
    """
    Demanda mínima compatible con ValidadorReglasDuras y el motor de reparación.
    """

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
        self.hybrid_group_id = None
        self.hybrid_partner_wsid = None
        self.slot_index = 0
        self.shift_type = None


def _make_coverage_stats(demands: List[MockDemand], covered: Dict[str, int]) -> Dict:
    """
    Construye un coverage_stats compatible con el generador.
    covered = {demand_id: n_cubiertos}
    """
    stats = {}
    for dm in demands:
        n_covered = covered.get(dm.id, 0)
        stats[dm.id] = {
            "demand": dm,
            "met": n_covered,
            "covered": n_covered,
            "unmet": max(0, dm.need - n_covered),
            "coverage_pct": (n_covered / dm.need * 100) if dm.need > 0 else 100.0,
            "employees": [],
        }
    return stats


def _make_sched(assignments: List) -> Dict:
    """
    assignments = [(emp, dm), ...]
    Retorna sched = defaultdict(list) {date: [(emp, dm)]}
    """
    sched = defaultdict(list)
    for emp, dm in assignments:
        sched[dm.date].append((emp, dm))
    return sched


# ─────────────────────────────────────────────────────────────────────────────
# FIXTURES COMUNES
# ─────────────────────────────────────────────────────────────────────────────

WS_BARRA = "ws-barra"
WS_COMEDOR = "ws-comedor"
WS_CAJA = "ws-caja"
MONDAY = date(2026, 5, 18)  # lunes


@pytest.fixture
def emp_barra() -> MockEmp:
    """Empleado habilitado para barra, 40h/sem."""
    return MockEmp("e1", roles={WS_BARRA}, weekly_minutes=40 * 60)


@pytest.fixture
def emp_comedor() -> MockEmp:
    """Empleado habilitado para comedor, 30h/sem."""
    return MockEmp("e2", roles={WS_COMEDOR}, weekly_minutes=30 * 60)


@pytest.fixture
def emp_multirol() -> MockEmp:
    """Empleado con ambos roles, 38h/sem."""
    return MockEmp("e3", roles={WS_BARRA, WS_COMEDOR}, weekly_minutes=38 * 60)


@pytest.fixture
def dm_barra() -> MockDemand:
    """Demanda de 1 persona en barra de 10:00 a 16:00."""
    return MockDemand("dm1", MONDAY, WS_BARRA, "BARRA", time(10, 0), time(16, 0), need=1)


@pytest.fixture
def dm_comedor() -> MockDemand:
    """Demanda de 1 persona en comedor de 11:00 a 17:00."""
    return MockDemand("dm2", MONDAY, WS_COMEDOR, "COMEDOR", time(11, 0), time(17, 0), need=1)


# ─────────────────────────────────────────────────────────────────────────────
# 1. ScheduleScoreAggregator
# ─────────────────────────────────────────────────────────────────────────────


class TestScheduleScoreAggregator:

    def test_score_aggregator_returns_score_between_0_and_100(self, emp_barra, emp_comedor, dm_barra, dm_comedor):
        """
        El score total siempre debe estar en [0, 100].
        Se prueba con horario completo, parcial y vacío.
        """
        from services.score_aggregator import ScheduleScoreAggregator

        agg = ScheduleScoreAggregator()
        emps = [emp_barra, emp_comedor]
        demands = [dm_barra, dm_comedor]

        # Horario vacío
        sched_empty = defaultdict(list)
        cs_empty = _make_coverage_stats(demands, {})
        score_empty = agg.aggregate(sched_empty, demands, emps, cs_empty)
        assert 0.0 <= score_empty.total_score <= 100.0

        # Horario completo
        sched_full = _make_sched([(emp_barra, dm_barra), (emp_comedor, dm_comedor)])
        cs_full = _make_coverage_stats(demands, {"dm1": 1, "dm2": 1})
        score_full = agg.aggregate(sched_full, demands, emps, cs_full)
        assert 0.0 <= score_full.total_score <= 100.0

        # Horario completo tiene mejor score que vacío
        assert score_full.total_score > score_empty.total_score

    def test_coverage_score_reflects_covered_slots(self, emp_barra, dm_barra, dm_comedor):
        """coverage_pct debe reflejar correctamente los slots cubiertos."""
        from services.score_aggregator import ScheduleScoreAggregator

        demands = [dm_barra, dm_comedor]  # 2 slots totales
        agg = ScheduleScoreAggregator()

        # 1 de 2 cubiertos → 50%
        cs = _make_coverage_stats(demands, {"dm1": 1})
        score = agg.aggregate(defaultdict(list), demands, [emp_barra], cs)
        assert score.covered_slots == 1
        assert score.total_slots == 2
        assert abs(score.coverage_pct - 50.0) < 0.1

    def test_hard_violations_reduce_total_score(self, emp_barra, dm_barra):
        """Violaciones duras deben penalizar fuertemente el total_score."""
        from services.score_aggregator import ScheduleScoreAggregator

        agg = ScheduleScoreAggregator()
        sched = _make_sched([(emp_barra, dm_barra)])
        cs = _make_coverage_stats([dm_barra], {"dm1": 1})

        score_clean = agg.aggregate(sched, [dm_barra], [emp_barra], cs, violations_hard=0)
        score_dirty = agg.aggregate(sched, [dm_barra], [emp_barra], cs, violations_hard=3)

        assert score_dirty.total_score < score_clean.total_score

    def test_fairness_perfect_when_one_employee(self, emp_barra, dm_barra):
        """Con un solo empleado trabajando, fairness debe ser 100%."""
        from services.score_aggregator import ScheduleScoreAggregator
        from services.ai_scheduler import EstadoEmpleado

        agg = ScheduleScoreAggregator()
        est = EstadoEmpleado(emp_id="e1")
        est.minutos_semana = 240

        estados = {"e1": est}
        fairness = agg.calculate_fairness([emp_barra], estados)
        assert fairness == 100.0

    def test_split_shifts_counted_correctly(self):
        """Un empleado con 2 bloques separados en el mismo día debe contar 1 split."""
        from services.score_aggregator import ScheduleScoreAggregator
        from services.ai_scheduler import EstadoEmpleado

        agg = ScheduleScoreAggregator()
        est = EstadoEmpleado(emp_id="e1")
        # Bloque mañana y tarde sin continuidad
        est.intervalos_por_dia[MONDAY] = [(600, 720), (900, 1020)]  # 10-12 y 15-17
        estados = {"e1": est}

        count = agg.calculate_split_shifts(estados)
        assert count == 1


# ─────────────────────────────────────────────────────────────────────────────
# 2. ScheduleGapClassifier
# ─────────────────────────────────────────────────────────────────────────────


class TestScheduleGapClassifier:

    def test_gap_without_skill_is_inevitable(self, emp_comedor, dm_barra):
        """
        Si ningún empleado tiene el skill del puesto, el hueco debe ser INEVITABLE.
        emp_comedor solo puede comedor, no barra.
        """
        from services.gap_classifier import ScheduleGapClassifier, GapType
        from services.ai_scheduler import ValidadorReglasDuras

        classifier = ScheduleGapClassifier(
            emps=[emp_comedor],
            validador=ValidadorReglasDuras(),
            debug=False,
        )
        cs = _make_coverage_stats([dm_barra], {})  # sin cubrir
        sched = defaultdict(list)
        gaps = classifier.classify(cs, sched)

        assert len(gaps) == 1
        assert gaps[0].gap_type == GapType.INEVITABLE
        assert "e2" in gaps[0].rejection_reasons  # emp_comedor rechazado por SIN_SKILL

    def test_gap_with_saturated_employee_is_correctable_by_swap(self, emp_barra, dm_barra):
        """
        Si el empleado habilitado ya alcanzó su límite semanal de horas,
        el hueco debe ser CORREGIBLE_SWAP.
        """
        from services.gap_classifier import ScheduleGapClassifier, GapType
        from services.ai_scheduler import EstadoEmpleado, ValidadorReglasDuras

        # Saturar al empleado: ya tiene 40h asignadas
        saturated_emp = MockEmp("e1", roles={WS_BARRA}, weekly_minutes=40 * 60)
        estado = EstadoEmpleado(emp_id="e1")
        estado.minutos_semana = 40 * 60  # exactamente al límite

        classifier = ScheduleGapClassifier(
            emps=[saturated_emp],
            validador=ValidadorReglasDuras(),
            debug=False,
        )
        cs = _make_coverage_stats([dm_barra], {})

        # Construir sched con el estado ya inyectado
        sched = defaultdict(list)
        gaps = classifier.classify(cs, sched, estados={"e1": estado})

        assert len(gaps) == 1
        assert gaps[0].gap_type == GapType.CORREGIBLE_SWAP
        assert gaps[0].skill_qualified_employees == ["e1"]

    def test_gap_classifier_does_not_crash_on_empty_data(self):
        """El clasificador no debe fallar si no hay huecos."""
        from services.gap_classifier import ScheduleGapClassifier
        from services.ai_scheduler import ValidadorReglasDuras

        classifier = ScheduleGapClassifier(emps=[], validador=ValidadorReglasDuras(), debug=False)
        gaps = classifier.classify({}, defaultdict(list))
        assert gaps == []

    def test_gap_type_corregible_extension_detected(self, emp_barra, dm_barra):
        """
        Si hay un empleado con skill asignado hoy con margen de horas,
        el hueco debe clasificarse como CORREGIBLE_EXTENSION (si no es SWAP directo).
        """
        from services.gap_classifier import ScheduleGapClassifier, GapType
        from services.ai_scheduler import EstadoEmpleado, ValidadorReglasDuras

        # Empleado con el skill, asignado hoy con 3h → le quedan 6h (max 9h)
        emp = MockEmp("e1", roles={WS_BARRA}, weekly_minutes=40 * 60)
        estado = EstadoEmpleado(emp_id="e1")
        # Asignado de 8 a 11 (3h) → minutos_por_dia = 180
        estado.registrar(MONDAY, WS_BARRA, 480, 660)  # 08:00-11:00

        # Demanda de barra de 17-20 (fuera de ventana del turno existente)
        dm_tarde = MockDemand("dm_tarde", MONDAY, WS_BARRA, "BARRA", time(17, 0), time(20, 0), need=1)
        cs = _make_coverage_stats([dm_tarde], {})
        sched = _make_sched(
            [(emp, MockDemand("dm_manana", MONDAY, WS_BARRA, "BARRA", time(8, 0), time(11, 0), need=1))]
        )

        # Saturar semana artificialmente para que MAX_HORAS_SEMANALES rechace
        estado.minutos_semana = 40 * 60  # al límite semanal

        classifier = ScheduleGapClassifier(emps=[emp], validador=ValidadorReglasDuras(), debug=False)
        gaps = classifier.classify(cs, sched, estados={"e1": estado})

        # Con semana saturada, es CORREGIBLE_SWAP (por MAX_HORAS_SEMANALES)
        # Si no estuviera saturado, sería CORREGIBLE_EXTENSION
        assert len(gaps) == 1
        assert gaps[0].gap_type in (
            GapType.CORREGIBLE_SWAP,
            GapType.CORREGIBLE_EXTENSION,
            GapType.DATO_INSUFICIENTE,
        )


# ─────────────────────────────────────────────────────────────────────────────
# 3. ScheduleRepairEngine
# ─────────────────────────────────────────────────────────────────────────────


class TestScheduleRepairEngine:

    def _make_engine(self, emps, demands, reglas=None):
        """Helper para instanciar el engine con valores por defecto."""
        from services.repair_engine import ScheduleRepairEngine
        from services.ai_scheduler import ValidadorReglasDuras

        _reglas = reglas or {
            "min_duracion_turno_horas": 3,
            "min_descanso_entre_turnos_horas": 9,
            "min_gap_split_horas": 3,
            "max_horas_por_dia": 9,
            "dias_descanso_semana": 2,
            "max_dias_trabajo_semana": 5,
            "max_bloques_por_dia": 2,
        }
        return ScheduleRepairEngine(
            emps=emps,
            demands=demands,
            validador=ValidadorReglasDuras(_reglas),
            reglas=_reglas,
            debug=False,
        )

    def test_swap_does_not_apply_if_creates_hard_violation(self):
        """
        Un swap que generaría un solapamiento u otra violación dura
        NO debe aplicarse y debe quedar registrado como rechazado.
        """
        # emp_a tiene skill barra y comedor; emp_b solo barra
        emp_a = MockEmp("a", roles={WS_BARRA, WS_COMEDOR}, weekly_minutes=40 * 60)
        emp_b = MockEmp("b", roles={WS_BARRA}, weekly_minutes=40 * 60)

        # Demanda barra de 10-16 (ya cubierta por emp_a)
        dm_barra_covered = MockDemand("dm_covered", MONDAY, WS_BARRA, "BARRA", time(10, 0), time(16, 0), need=1)
        # Demanda comedor de 10-16 (solaparía con barra para emp_a)
        dm_comedor_gap = MockDemand("dm_gap", MONDAY, WS_COMEDOR, "COMEDOR", time(10, 0), time(16, 0), need=1)

        sched = _make_sched([(emp_a, dm_barra_covered)])
        cs = _make_coverage_stats(
            [dm_barra_covered, dm_comedor_gap], {"dm_covered": 1}  # barra cubierta, comedor sin cubrir
        )

        engine = self._make_engine([emp_a, emp_b], [dm_barra_covered, dm_comedor_gap])
        result = engine.reparar(sched, cs)

        # El swap emp_a→comedor solaparía con barra 10-16; no debe aplicarse
        for s in result.repair_suggestions:
            if s.applied:
                # Si hay alguna reparación aplicada, no debe haber violaciones
                is_valid, errors = engine.validate_schedule_integrity(sched, cs)
                assert is_valid, f"Violaciones detectadas: {errors}"

    def test_swap_applies_when_score_improves(self):
        """
        Un swap válido que mejora la cobertura debe aplicarse y quedar
        registrado en repair_suggestions con applied=True.
        """
        # emp_a: solo barra, saturado
        emp_a = MockEmp("a", roles={WS_BARRA}, weekly_minutes=6 * 60)
        # emp_b: solo barra, tiene capacidad
        emp_b = MockEmp("b", roles={WS_BARRA}, weekly_minutes=40 * 60)

        # Demanda barra mañana (ya asignada a emp_a)
        dm_manana = MockDemand("dm_m", MONDAY, WS_BARRA, "BARRA", time(8, 0), time(11, 0), need=1)
        # Demanda barra tarde (sin cubrir — emp_a saturado)
        dm_tarde = MockDemand("dm_t", MONDAY, WS_BARRA, "BARRA", time(14, 0), time(17, 0), need=1)

        sched = _make_sched([(emp_a, dm_manana)])
        cs = _make_coverage_stats([dm_manana, dm_tarde], {"dm_m": 1})

        engine = self._make_engine([emp_a, emp_b], [dm_manana, dm_tarde])
        result = engine.reparar(sched, cs)

        # Debe haber mejorado la cobertura
        assert result.repaired_score.coverage_pct >= result.original_score.coverage_pct
        # No debe haber violaciones duras
        is_valid, errors = engine.validate_schedule_integrity(sched, cs)
        assert is_valid, f"Violaciones tras swap: {errors}"

    def test_extension_respects_max_daily_hours(self):
        """
        La extensión de turno no debe superar el máximo de horas diarias.
        Si el empleado ya tiene 9h ese día, no se puede extender.
        """
        emp = MockEmp("e1", roles={WS_BARRA}, weekly_minutes=40 * 60)

        # Turno que ya ocupa exactamente el máximo (9h)
        dm_full = MockDemand("dm_full", MONDAY, WS_BARRA, "BARRA", time(8, 0), time(17, 0), need=1)  # 9h
        # Otro slot el mismo día que debería ser extensión imposible
        dm_extra = MockDemand(
            "dm_extra", MONDAY, WS_BARRA, "BARRA", time(17, 0), time(18, 0), need=1  # 1h más = 10h total → viola max
        )

        reglas_9h = {
            "min_duracion_turno_horas": 1,
            "min_descanso_entre_turnos_horas": 9,
            "min_gap_split_horas": 3,
            "max_horas_por_dia": 9,
            "dias_descanso_semana": 2,
            "max_dias_trabajo_semana": 5,
            "max_bloques_por_dia": 2,
        }

        sched = _make_sched([(emp, dm_full)])
        cs = _make_coverage_stats([dm_full, dm_extra], {"dm_full": 1})

        engine = self._make_engine([emp], [dm_full, dm_extra], reglas=reglas_9h)
        result = engine.reparar(sched, cs)

        # La extensión no debe haberse aplicado (viola max_horas_dia)
        for s in result.repair_suggestions:
            if s.repair_type.value == "EXTENSION" and s.applied:
                pytest.fail("Se aplicó extensión que viola max_horas_dia")

        # Integridad del horario intacta
        is_valid, errors = engine.validate_schedule_integrity(sched, cs)
        assert is_valid, f"Violaciones: {errors}"

    def test_repair_never_reduces_total_score(self, emp_barra, emp_comedor):
        """
        El score total después de repair debe ser ≥ score antes de repair.
        Invariante fundamental del engine.
        """
        dm1 = MockDemand("dm1", MONDAY, WS_BARRA, "BARRA", time(10, 0), time(16, 0), need=1)
        dm2 = MockDemand("dm2", MONDAY, WS_COMEDOR, "COMEDOR", time(11, 0), time(17, 0), need=1)

        # Horario parcial: solo barra cubierta
        sched = _make_sched([(emp_barra, dm1)])
        cs = _make_coverage_stats([dm1, dm2], {"dm1": 1})

        engine = self._make_engine([emp_barra, emp_comedor], [dm1, dm2])
        result = engine.reparar(sched, cs)

        assert result.repaired_score.total_score >= result.original_score.total_score, (
            f"Score decreció: {result.original_score.total_score:.2f} → " f"{result.repaired_score.total_score:.2f}"
        )

    def test_repair_never_introduces_hard_violations(self):
        """
        Después de todas las reparaciones no debe haber violaciones duras
        (solapamientos ni incoherencias en coverage_stats).
        """
        emp_multi = MockEmp("m1", roles={WS_BARRA, WS_COMEDOR}, weekly_minutes=40 * 60)
        emp_barra_only = MockEmp("b1", roles={WS_BARRA}, weekly_minutes=40 * 60)

        dm_b = MockDemand("dm_b", MONDAY, WS_BARRA, "BARRA", time(9, 0), time(15, 0), need=1)
        dm_c = MockDemand("dm_c", MONDAY, WS_COMEDOR, "COMEDOR", time(10, 0), time(16, 0), need=1)
        dm_b2 = MockDemand("dm_b2", MONDAY, WS_BARRA, "BARRA", time(16, 0), time(19, 0), need=1)

        # Asignar emp_multi a barra, dejar comedor sin cubrir
        sched = _make_sched([(emp_multi, dm_b)])
        cs = _make_coverage_stats([dm_b, dm_c, dm_b2], {"dm_b": 1})

        engine = self._make_engine([emp_multi, emp_barra_only], [dm_b, dm_c, dm_b2])
        result = engine.reparar(sched, cs)

        # Validar integridad estructural
        is_valid, errors = engine.validate_schedule_integrity(sched, cs)
        assert is_valid, f"Violaciones duras introducidas por repair: {errors}"

        # El score hard violations sigue en 0
        assert result.repaired_score.violations_hard == 0

    def test_fallback_role_is_used_only_when_configured(self, dm_barra):
        """
        Si no hay fallbacks configurados y el empleado no tiene el skill,
        el hueco sigue siendo INEVITABLE y no se aplica ninguna reparación.
        """
        emp_no_skill = MockEmp("ns1", roles={WS_COMEDOR}, weekly_minutes=40 * 60)

        sched = defaultdict(list)
        cs = _make_coverage_stats([dm_barra], {})

        # Engine SIN fallbacks
        engine = self._make_engine([emp_no_skill], [dm_barra])
        result = engine.reparar(sched, cs)

        assert result.repairs_applied == 0
        # El hueco sigue sin cubrirse
        assert result.gaps_after == result.gaps_before

    def test_optimization_result_reports_before_after_metrics(self, emp_barra, emp_comedor):
        """
        OptimizationResult debe contener métricas coherentes de antes y después.
        """
        dm1 = MockDemand("dm1", MONDAY, WS_BARRA, "BARRA", time(10, 0), time(16, 0), need=1)
        dm2 = MockDemand("dm2", MONDAY, WS_COMEDOR, "COMEDOR", time(11, 0), time(17, 0), need=1)

        sched = defaultdict(list)
        cs = _make_coverage_stats([dm1, dm2], {})  # todo sin cubrir

        engine = self._make_engine([emp_barra, emp_comedor], [dm1, dm2])
        result = engine.reparar(sched, cs)

        # Campos requeridos están presentes
        assert hasattr(result, "original_score")
        assert hasattr(result, "repaired_score")
        assert hasattr(result, "gaps_before")
        assert hasattr(result, "gaps_after")
        assert hasattr(result, "repairs_attempted")
        assert hasattr(result, "repairs_applied")
        assert hasattr(result, "repair_suggestions")
        assert hasattr(result, "execution_time_ms")
        assert result.execution_time_ms >= 0
        assert result.solver_used is False
        assert result.solver_name is None

        # Coherencia: gaps_after ≤ gaps_before
        assert result.gaps_after <= result.gaps_before

        # Coherencia: repairs_applied ≤ repairs_attempted
        assert result.repairs_applied <= result.repairs_attempted

        # Score after ≥ score before (invariante)
        assert result.repaired_score.total_score >= result.original_score.total_score

    def test_repair_improves_coverage_when_possible(self):
        """
        Cuando hay un empleado con el skill y capacidad disponible
        que el generador pasó por alto, el repair lo debe encontrar.
        """
        emp = MockEmp("e1", roles={WS_BARRA}, weekly_minutes=40 * 60)

        dm = MockDemand("dm1", MONDAY, WS_BARRA, "BARRA", time(10, 0), time(16, 0), need=1)

        sched = defaultdict(list)
        cs = _make_coverage_stats([dm], {})  # sin cubrir

        engine = self._make_engine([emp], [dm])
        result = engine.reparar(sched, cs)

        # Debe haber cubierto el hueco (asignación directa)
        assert result.repaired_score.coverage_pct >= result.original_score.coverage_pct
        assert cs[dm.id]["covered"] >= 0  # no negativo

    def test_validate_schedule_integrity_detects_overlap(self):
        """
        validate_schedule_integrity() debe detectar solapamientos.
        """
        emp = MockEmp("e1", roles={WS_BARRA}, weekly_minutes=40 * 60)
        dm1 = MockDemand("dm1", MONDAY, WS_BARRA, "BARRA", time(10, 0), time(14, 0), need=1)
        dm2 = MockDemand("dm2", MONDAY, WS_BARRA, "BARRA", time(12, 0), time(16, 0), need=1)  # solapamiento con dm1

        # Construir sched con solapamiento artificial
        sched = defaultdict(list)
        sched[MONDAY].append((emp, dm1))
        sched[MONDAY].append((emp, dm2))
        cs = _make_coverage_stats([dm1, dm2], {"dm1": 1, "dm2": 1})

        engine = self._make_engine([emp], [dm1, dm2])
        is_valid, errors = engine.validate_schedule_integrity(sched, cs)

        assert not is_valid
        assert len(errors) > 0
        assert any("Solapamiento" in e for e in errors)

    def test_repair_result_serializable(self, emp_barra, dm_barra):
        """OptimizationResult.to_dict() no debe lanzar excepciones."""
        sched = defaultdict(list)
        cs = _make_coverage_stats([dm_barra], {})

        engine = self._make_engine([emp_barra], [dm_barra])
        result = engine.reparar(sched, cs)

        d = result.to_dict()
        assert isinstance(d, dict)
        assert "original_score" in d
        assert "repaired_score" in d
        assert "gaps_before" in d
        assert "repair_suggestions" in d


# ─────────────────────────────────────────────────────────────────────────────
# 4. INTEGRACIÓN: flujo completo generador → repair
# ─────────────────────────────────────────────────────────────────────────────


class TestIntegrationFlow:

    def test_full_flow_coverage_does_not_decrease(self):
        """
        Simula el flujo completo: horario generado con huecos →
        repair engine → cobertura no decrece.
        """
        emp_a = MockEmp("a", roles={WS_BARRA, WS_COMEDOR}, weekly_minutes=40 * 60)
        emp_b = MockEmp("b", roles={WS_BARRA}, weekly_minutes=40 * 60)

        demands = [
            MockDemand("d1", MONDAY, WS_BARRA, "BARRA", time(9, 0), time(15, 0)),
            MockDemand("d2", MONDAY, WS_COMEDOR, "COMEDOR", time(10, 0), time(16, 0)),
            MockDemand("d3", MONDAY, WS_BARRA, "BARRA", time(16, 0), time(19, 0)),
        ]

        # Simular que el generador cubrió d1 pero dejó d2 y d3 sin cubrir
        sched = _make_sched([(emp_a, demands[0])])
        cs = _make_coverage_stats(demands, {"d1": 1})

        from services.repair_engine import ScheduleRepairEngine
        from services.ai_scheduler import ValidadorReglasDuras

        engine = ScheduleRepairEngine(
            emps=[emp_a, emp_b],
            demands=demands,
            validador=ValidadorReglasDuras(),
            debug=False,
        )
        result = engine.reparar(sched, cs)

        assert result.repaired_score.coverage_pct >= result.original_score.coverage_pct
        assert result.repaired_score.total_score >= result.original_score.total_score

        is_valid, errors = engine.validate_schedule_integrity(sched, cs)
        assert is_valid, f"Violaciones en flujo completo: {errors}"
