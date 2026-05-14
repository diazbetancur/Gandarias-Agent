# services/skill_coverage_analyzer.py
"""
SkillCoverageAnalyzer — Gandarias v5.0
========================================
Analiza la cobertura por skill/workstation y distingue dos tipos de déficit:

  DÉFICIT ESTRUCTURAL: No hay suficiente personal capacitado en el sistema.
      El algoritmo no puede resolver esto —se necesita contratar o capacitar.

  DÉFICIT ALGORÍTMICO: Hay candidatos disponibles, pero el greedy no los asignó
      (conflicto de balance, decisión subóptima). El RepairEngine puede atacarlo.

El analizador es READ-ONLY: no modifica el horario, ni el RepairEngine, ni el
generador. Es un módulo de diagnóstico e inteligencia operativa.

Salida principal:
    List[SkillCoverageSummary]  — resumen por workstation
    List[TrainingRecommendation] — recomendaciones de capacitación/contratación
    Dict                        — reporte ejecutivo completo (to_report_dict)

Ejecutar análisis:
    analyzer = SkillCoverageAnalyzer(role_fallbacks=ROLE_FALLBACKS)
    summaries = analyzer.analyze(emps, demands, sched, coverage_stats)
    recommendations = analyzer.recommend_training(summaries, emps)
    report = analyzer.to_report_dict(summaries, recommendations)
"""

from __future__ import annotations

import logging
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import date, time
from enum import Enum
from typing import Any, Dict, List, Optional, Set, Tuple

from services.ai_scheduler import (
    EstadoEmpleado,
    ValidadorReglasDuras,
    _end_min,
    _seg_min,
    _t2m,
    REGLAS_DURAS_DEFAULTS,
)

logger = logging.getLogger("skill_coverage_analyzer")

# ─────────────────────────────────────────────────────────────────────────────
# UMBRALES DE SEVERIDAD
# ─────────────────────────────────────────────────────────────────────────────

_SEV_CRITICAL_MAX_COVERAGE = 80.0  # < 80% → CRITICAL
_SEV_HIGH_MAX_COVERAGE = 90.0  # 80-90% → HIGH
_SEV_MEDIUM_MAX_COVERAGE = 95.0  # 90-95% → MEDIUM
_SEV_LOW_MAX_POOL = 2  # qualified_pool_size <= 2 → HIGH
_RECURRENT_THRESHOLD = 2  # misma franja >= N semanas → recurrente

# Razones de rechazo del ValidadorReglasDuras
_SKILL_REASONS: Set[str] = {"SIN_SKILL"}
_HOURS_REASONS: Set[str] = {"MAX_HORAS_SEMANALES", "MAX_DIAS", "MAX_HORAS_DIA"}
_WINDOW_REASONS: Set[str] = {"FUERA_VENTANA", "FUERA_USERSHIFT_WINDOW"}
_AVAIL_REASONS: Set[str] = {"DIA_LIBRE", "ABS"}
_ALL_BLOCKING: Set[str] = _SKILL_REASONS | _HOURS_REASONS | _WINDOW_REASONS | _AVAIL_REASONS


# ─────────────────────────────────────────────────────────────────────────────
# ENUMS
# ─────────────────────────────────────────────────────────────────────────────


class DeficitType(str, Enum):
    """Tipo de déficit de cobertura por workstation."""

    STRUCTURAL_NO_SKILL = "STRUCTURAL_NO_SKILL"
    STRUCTURAL_TOO_FEW_QUALIFIED = "STRUCTURAL_TOO_FEW_QUALIFIED"
    AVAILABILITY_GAP = "AVAILABILITY_GAP"
    HOURS_LIMIT_GAP = "HOURS_LIMIT_GAP"
    ALGORITHMIC_GAP = "ALGORITHMIC_GAP"
    DATA_QUALITY_GAP = "DATA_QUALITY_GAP"


class Severity(str, Enum):
    CRITICAL = "CRITICAL"
    HIGH = "HIGH"
    MEDIUM = "MEDIUM"
    LOW = "LOW"


# ─────────────────────────────────────────────────────────────────────────────
# DTOs
# ─────────────────────────────────────────────────────────────────────────────


@dataclass
class SkillCoverageGap:
    """
    Análisis de un único slot de demanda sin cubrir.

    Campos de diagnóstico:
        qualified_employees_count   — Empleados con el skill requerido (pool total)
        available_qualified_count   — Calificados Y disponibles (no ausentes, no día libre)
        unavailable_qualified_count — Calificados pero fuera de ventana/ausentes
        blocked_by_hours_count      — Calificados bloqueados por límite de horas
        blocked_by_window_count     — Bloqueados por ventana de disponibilidad
        blocked_by_day_off_count    — Bloqueados por día libre
        blocked_by_absence_count    — Bloqueados por ausencia registrada
        deficit_type                — Clasificación del tipo de déficit
        severity                    — CRITICAL / HIGH / MEDIUM / LOW
        dow                         — Día de semana (0=Lun, 6=Dom)
    """

    workstation_id: Any
    workstation_name: str
    date: date
    dow: int  # 0=Lun, 6=Dom
    start_time: time
    end_time: time
    required_staff: int
    covered_staff: int
    missing_staff: int
    qualified_employees_count: int
    available_qualified_count: int
    unavailable_qualified_count: int
    blocked_by_hours_count: int
    blocked_by_window_count: int
    blocked_by_day_off_count: int
    blocked_by_absence_count: int
    deficit_type: DeficitType
    severity: Severity
    demand_id: Any = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "workstation_id": str(self.workstation_id),
            "workstation_name": self.workstation_name,
            "date": self.date.isoformat(),
            "dow": self.dow,
            "dow_name": _DOW_NAMES[self.dow],
            "start_time": self.start_time.isoformat(),
            "end_time": self.end_time.isoformat(),
            "required_staff": self.required_staff,
            "covered_staff": self.covered_staff,
            "missing_staff": self.missing_staff,
            "qualified_employees_count": self.qualified_employees_count,
            "available_qualified_count": self.available_qualified_count,
            "unavailable_qualified_count": self.unavailable_qualified_count,
            "blocked_by_hours_count": self.blocked_by_hours_count,
            "blocked_by_window_count": self.blocked_by_window_count,
            "blocked_by_day_off_count": self.blocked_by_day_off_count,
            "blocked_by_absence_count": self.blocked_by_absence_count,
            "deficit_type": self.deficit_type.value,
            "severity": self.severity.value,
            "demand_id": str(self.demand_id) if self.demand_id else None,
        }


@dataclass
class SkillCoverageSummary:
    """
    Resumen de cobertura de una workstation para el período analizado.

    structural_deficit: True si hay más slots con STRUCTURAL_NO_SKILL o
    STRUCTURAL_TOO_FEW_QUALIFIED que con otros tipos de déficit.
    """

    workstation_id: Any
    workstation_name: str
    total_required_slots: int
    total_covered_slots: int
    total_missing_slots: int
    coverage_pct: float
    qualified_pool_size: int  # Empleados únicos con el skill
    recurrent_gap_count: int  # Huecos que siguen el mismo patrón DOW+hora
    worst_days: List[str]  # ISO dates con mayor cobertura faltante
    worst_time_ranges: List[str]  # "HH:MM-HH:MM" con mayor faltante
    structural_deficit: bool  # True si el déficit es mayormente estructural
    primary_deficit_type: DeficitType
    severity: Severity
    gaps: List[SkillCoverageGap] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "workstation_id": str(self.workstation_id),
            "workstation_name": self.workstation_name,
            "total_required_slots": self.total_required_slots,
            "total_covered_slots": self.total_covered_slots,
            "total_missing_slots": self.total_missing_slots,
            "coverage_pct": round(self.coverage_pct, 1),
            "qualified_pool_size": self.qualified_pool_size,
            "recurrent_gap_count": self.recurrent_gap_count,
            "worst_days": self.worst_days,
            "worst_time_ranges": self.worst_time_ranges,
            "structural_deficit": self.structural_deficit,
            "primary_deficit_type": self.primary_deficit_type.value,
            "severity": self.severity.value,
            "gaps": [g.to_dict() for g in self.gaps],
        }


@dataclass
class TrainingRecommendation:
    """
    Recomendación operativa de capacitación o contratación para una workstation.

    minimum_additional_people_needed: número mínimo de personas adicionales
    con el skill para cubrir los huecos estructurales.

    suggested_employees_to_train: empleados actuales que podrían ser capacitados
    (tienen roles de fallback o roles cercanos). Puede estar vacío si no hay
    candidatos adecuados → señal de que se necesita contratar.
    """

    workstation_id: Any
    workstation_name: str
    minimum_additional_people_needed: int
    suggested_employees_to_train: List[str]  # emp names/ids
    reason: str
    expected_coverage_gain_estimate: float  # 0.0 a 100.0 puntos porcentuales

    def to_dict(self) -> Dict[str, Any]:
        return {
            "workstation_id": str(self.workstation_id),
            "workstation_name": self.workstation_name,
            "minimum_additional_people_needed": self.minimum_additional_people_needed,
            "suggested_employees_to_train": self.suggested_employees_to_train,
            "reason": self.reason,
            "expected_coverage_gain_estimate": round(self.expected_coverage_gain_estimate, 1),
        }


# ─────────────────────────────────────────────────────────────────────────────
# ADAPTADOR INTERNO DE DEMANDA
# ─────────────────────────────────────────────────────────────────────────────


class _DemandAdapter:
    """Adaptador mínimo para pasar demandas a ValidadorReglasDuras."""

    __slots__ = (
        "id",
        "date",
        "wsid",
        "wsname",
        "start",
        "end",
        "need",
        "raw_need",
        "has_hybrid_component",
        "observation_override",
        "user_shift_windows",
        "hybrid_group_id",
        "shift_type",
        "slot_index",
    )

    def __init__(self, dm: Any):
        self.id = dm.id
        self.date = dm.date
        self.wsid = getattr(dm, "wsid", getattr(dm, "workstation_id", None))
        self.wsname = getattr(dm, "wsname", getattr(dm, "workstation_name", ""))
        self.start = getattr(dm, "start", getattr(dm, "start_time", None))
        self.end = getattr(dm, "end", getattr(dm, "end_time", None))
        self.need = getattr(dm, "need", getattr(dm, "required_staff", 1))
        self.raw_need = float(self.need)
        self.has_hybrid_component = getattr(dm, "has_hybrid_component", False)
        self.observation_override = getattr(dm, "observation_override", None)
        self.user_shift_windows = getattr(dm, "user_shift_windows", {})
        self.hybrid_group_id = getattr(dm, "hybrid_group_id", None)
        self.shift_type = getattr(dm, "shift_type", None)
        self.slot_index = getattr(dm, "slot_index", 0)


# ─────────────────────────────────────────────────────────────────────────────
# HELPERS
# ─────────────────────────────────────────────────────────────────────────────

_DOW_NAMES = ["Lunes", "Martes", "Miércoles", "Jueves", "Viernes", "Sábado", "Domingo"]


def _compute_severity(coverage_pct: float, qualified_pool: int, recurrent: bool, is_critical_ws: bool) -> Severity:
    """Aplica las reglas de severidad según la especificación."""
    if coverage_pct < _SEV_CRITICAL_MAX_COVERAGE or qualified_pool == 0 or (recurrent and is_critical_ws):
        return Severity.CRITICAL
    if coverage_pct < _SEV_HIGH_MAX_COVERAGE or qualified_pool <= _SEV_LOW_MAX_POOL:
        return Severity.HIGH
    if coverage_pct < _SEV_MEDIUM_MAX_COVERAGE:
        return Severity.MEDIUM
    return Severity.LOW


def _reconstruct_estados(
    sched: Dict[date, List[Tuple[Any, Any]]],
    reglas: Optional[Dict] = None,
) -> Dict[str, EstadoEmpleado]:
    """
    Reconstruye los EstadoEmpleado desde el horario generado.
    Usado para saber cuántas horas lleva cada empleado.
    """
    estados: Dict[str, EstadoEmpleado] = {}
    for d, asignaciones in sched.items():
        for emp, dm in asignaciones:
            key = str(emp.id)
            if key not in estados:
                estados[key] = EstadoEmpleado(emp_id=str(emp.id))
            ws_id = getattr(dm, "wsid", getattr(dm, "workstation_id", None))
            s_t = getattr(dm, "start", getattr(dm, "start_time", None))
            e_t = getattr(dm, "end", getattr(dm, "end_time", None))
            if s_t and e_t:
                s_m = _t2m(s_t)
                e_m = _end_min(e_t)
                estados[key].registrar(d, str(ws_id), s_m, e_m)
    return estados


# ─────────────────────────────────────────────────────────────────────────────
# CORE ANALYZER
# ─────────────────────────────────────────────────────────────────────────────


class SkillCoverageAnalyzer:
    """
    Analiza la cobertura por skill/workstation y produce diagnóstico
    diferenciando déficit estructural de déficit algorítmico.

    Parámetros del constructor:
        role_fallbacks  — Dict[ws_name, List[ws_name]] de roles con fallback.
                          Mismo formato que ROLE_FALLBACKS_BY_NAME en agenda.py.
        reglas          — Reglas duras (usa REGLAS_DURAS_DEFAULTS si None).
        debug           — Activa logging detallado.
    """

    def __init__(
        self,
        role_fallbacks: Optional[Dict[str, List[str]]] = None,
        reglas: Optional[Dict] = None,
        debug: bool = False,
    ):
        self._role_fallbacks = role_fallbacks or {}
        self._reglas = reglas or REGLAS_DURAS_DEFAULTS
        self._debug = debug
        self._validador = ValidadorReglasDuras(self._reglas)

    # ─── MÉTODO PRINCIPAL ────────────────────────────────────────────────────

    def analyze(
        self,
        emps: List[Any],
        demands: List[Any],
        sched: Dict[date, List[Tuple[Any, Any]]],
        coverage_stats: Dict[Any, Dict[str, Any]],
        external_rejection_reasons: Optional[Dict[str, Dict[str, int]]] = None,
    ) -> List[SkillCoverageSummary]:
        """
        Analiza la cobertura por workstation y devuelve un resumen por ws.

        Parámetros:
            emps              — Lista de empleados (duck-typing: .id, .can(), .off(), ...)
            demands           — Lista de demandas del período
            sched             — Horario generado {date: [(emp, demand)]}
            coverage_stats    — {demand_id: {demand, covered, unmet, ...}}
            external_rejection_reasons — {ws_name: {SKILL_FALTANTE: N, ...}}
                                         Opcional: razones de rechazo externas
                                         (p.ej. del campo GapExplanation de huecos.csv).
                                         Si se provee, enriquece la clasificación.

        Retorna:
            List[SkillCoverageSummary] ordenado por cobertura ascendente
            (peor workstation primero).
        """
        # Reconstruir estados desde el horario para saber horas usadas
        estados = _reconstruct_estados(sched, self._reglas)

        # Mapa de empleados por ID
        emps_by_id = {str(e.id): e for e in emps}

        # Identificar demandas con huecos (unmet > 0 en coverage_stats)
        gap_demands: List[Any] = []
        for dm_id, cs in coverage_stats.items():
            unmet = cs.get("unmet", 0)
            if unmet > 0:
                dm = cs.get("demand")
                if dm:
                    gap_demands.append((dm, unmet))

        # Si no hay huecos, retornar lista vacía (100% cobertura global)
        if not gap_demands:
            logger.debug("analyze(): no gap demands found — 100%% coverage")
            return []

        # Agrupar huecos por workstation
        by_ws: Dict[str, List] = defaultdict(list)
        for dm, missing in gap_demands:
            ws_id = str(getattr(dm, "wsid", getattr(dm, "workstation_id", "")))
            by_ws[ws_id].append((dm, missing))

        # Pool de skill por ws (calculado una vez)
        skill_pool_by_ws: Dict[str, List[Any]] = {}
        for ws_id in by_ws:
            skill_pool_by_ws[ws_id] = [e for e in emps if self._can(e, ws_id)]

        # Analizar cada hueco individual
        all_gaps: Dict[str, List[SkillCoverageGap]] = defaultdict(list)
        for ws_id, dm_list in by_ws.items():
            qualified_emps = skill_pool_by_ws[ws_id]
            for dm, missing in dm_list:
                gap = self._analyze_gap(dm, missing, qualified_emps, estados, emps, ws_id)
                all_gaps[ws_id].append(gap)

        # Detectar patrones recurrentes (por DOW × franja horaria)
        recurrent_keys = self._detect_recurrent_keys(all_gaps)

        # Construir resúmenes por workstation
        summaries: List[SkillCoverageSummary] = []
        all_demands_by_ws: Dict[str, int] = defaultdict(int)
        all_covered_by_ws: Dict[str, int] = defaultdict(int)

        # Totalizar desde demands (no solo los huecos)
        for dm_id, cs in coverage_stats.items():
            dm = cs.get("demand")
            if not dm:
                continue
            ws_id = str(getattr(dm, "wsid", getattr(dm, "workstation_id", "")))
            all_demands_by_ws[ws_id] += getattr(dm, "need", 1)
            all_covered_by_ws[ws_id] += cs.get("covered", 0)

        for ws_id, gaps in all_gaps.items():
            ws_name = gaps[0].workstation_name if gaps else ws_id
            pool = skill_pool_by_ws[ws_id]
            total_req = all_demands_by_ws.get(ws_id, sum(g.required_staff for g in gaps))
            total_cov = all_covered_by_ws.get(ws_id, sum(g.covered_staff for g in gaps))
            total_miss = sum(g.missing_staff for g in gaps)
            coverage_pct = (total_cov / max(1, total_req)) * 100.0

            # Recurrentes: cuántos de los gaps de esta ws siguen un patrón repetido
            recurrent_count = sum(1 for g in gaps if _gap_recurrent_key(g) in recurrent_keys)

            worst_days = _worst_days(gaps, top_n=3)
            worst_ranges = _worst_time_ranges(gaps, top_n=3)

            primary_type = self._primary_deficit_type(gaps, pool)
            is_structural = primary_type in (
                DeficitType.STRUCTURAL_NO_SKILL,
                DeficitType.STRUCTURAL_TOO_FEW_QUALIFIED,
            )
            sev = _compute_severity(
                coverage_pct,
                len(pool),
                recurrent_count > 0,
                is_critical_ws=len(pool) == 0,
            )

            summaries.append(
                SkillCoverageSummary(
                    workstation_id=ws_id,
                    workstation_name=ws_name,
                    total_required_slots=total_req,
                    total_covered_slots=total_cov,
                    total_missing_slots=total_miss,
                    coverage_pct=coverage_pct,
                    qualified_pool_size=len(pool),
                    recurrent_gap_count=recurrent_count,
                    worst_days=worst_days,
                    worst_time_ranges=worst_ranges,
                    structural_deficit=is_structural,
                    primary_deficit_type=primary_type,
                    severity=sev,
                    gaps=gaps,
                )
            )

        # Ordenar: peor cobertura primero
        summaries.sort(key=lambda s: s.coverage_pct)
        return summaries

    # ─── CLASIFICACIÓN DE DÉFICIT ─────────────────────────────────────────────

    def classify_deficit(
        self,
        qualified_pool_size: int,
        blocked_by_hours: int,
        blocked_by_window: int,
        blocked_by_day_off: int,
        blocked_by_absence: int,
        available_qualified: int,
        missing_staff: int,
    ) -> DeficitType:
        """
        Clasifica el tipo de déficit de cobertura para un slot dado.

        Lógica de clasificación (en orden de prioridad):

        1. Sin ningún empleado calificado → STRUCTURAL_NO_SKILL
        2. Pool ≤ 2 → STRUCTURAL_TOO_FEW_QUALIFIED
        3. El pool suficiente pero todos en ventana/día libre/ausencia → AVAILABILITY_GAP
        4. El pool suficiente pero todos en tope de horas → HOURS_LIMIT_GAP
        5. Hay calificados disponibles pero sin asignar → ALGORITHMIC_GAP
        6. No hay suficiente información → DATA_QUALITY_GAP
        """
        if qualified_pool_size == 0:
            return DeficitType.STRUCTURAL_NO_SKILL

        if qualified_pool_size <= _SEV_LOW_MAX_POOL:
            # Pool muy pequeño → riesgo estructural aunque alguno esté disponible
            return DeficitType.STRUCTURAL_TOO_FEW_QUALIFIED

        total_blocked = blocked_by_hours + blocked_by_window + blocked_by_day_off + blocked_by_absence
        if total_blocked == 0 and available_qualified >= missing_staff:
            # Candidatos disponibles no asignados → el greedy los pasó por alto
            return DeficitType.ALGORITHMIC_GAP

        if blocked_by_hours > 0 and (blocked_by_window + blocked_by_day_off + blocked_by_absence) == 0:
            return DeficitType.HOURS_LIMIT_GAP

        if (blocked_by_window + blocked_by_day_off + blocked_by_absence) > 0 and blocked_by_hours == 0:
            return DeficitType.AVAILABILITY_GAP

        # Mezcla de razones → usar la predominante o marcar como DATA_QUALITY
        if total_blocked > 0:
            counts = {
                "hours": blocked_by_hours,
                "window": blocked_by_window + blocked_by_day_off + blocked_by_absence,
            }
            dominant = max(counts, key=counts.get)  # type: ignore[arg-type]
            if dominant == "hours":
                return DeficitType.HOURS_LIMIT_GAP
            return DeficitType.AVAILABILITY_GAP

        return DeficitType.DATA_QUALITY_GAP

    # ─── DETECCIÓN DE PATRONES RECURRENTES ──────────────────────────────────

    def detect_recurrent_gaps(
        self,
        gaps_by_ws: Dict[str, List[SkillCoverageGap]],
        threshold: int = _RECURRENT_THRESHOLD,
    ) -> Dict[str, List[SkillCoverageGap]]:
        """
        Agrupa los huecos por (workstation, día_de_semana, franja_horaria).
        Retorna los grupos donde count >= threshold (patrones recurrentes).

        La clave de agrupación es: f"{ws_id}|{dow}|{time_bucket}"
        donde time_bucket redondea al bloque de 30 minutos.

        Parámetros:
            gaps_by_ws — {ws_id: [SkillCoverageGap]}
            threshold  — mínimo de ocurrencias para considerar recurrente

        Retorna:
            {clave_patron: [SkillCoverageGap]} — solo los grupos con >= threshold
        """
        buckets: Dict[str, List[SkillCoverageGap]] = defaultdict(list)
        for ws_id, gaps in gaps_by_ws.items():
            for g in gaps:
                key = _gap_recurrent_key(g)
                buckets[key].append(g)

        return {k: v for k, v in buckets.items() if len(v) >= threshold}

    # ─── RECOMENDACIONES DE CAPACITACIÓN ─────────────────────────────────────

    def recommend_training(
        self,
        summaries: List[SkillCoverageSummary],
        emps: Optional[List[Any]] = None,
    ) -> List[TrainingRecommendation]:
        """
        Genera recomendaciones de capacitación o contratación para las
        workstations con déficit estructural.

        Lógica:
        - Para cada ws con structural_deficit=True:
          1. Calcula cuántas personas adicionales se necesitan para cubrir
             el pico de demanda simultánea faltante.
          2. Si hay `role_fallbacks` configurados para esa ws, busca empleados
             que tengan esos roles alternativos → candidatos de capacitación.
          3. Si no hay candidatos internos → recomendar contratación externa.

        Parámetros:
            summaries — resultado de analyze()
            emps      — lista de empleados (para buscar candidatos internos)

        Retorna:
            List[TrainingRecommendation] ordenado por impacto (mayor faltante primero)
        """
        recs: List[TrainingRecommendation] = []
        emps = emps or []

        for summary in summaries:
            if not summary.structural_deficit:
                continue
            if summary.total_missing_slots == 0:
                continue

            ws_name = summary.workstation_name
            ws_id = summary.workstation_id

            # Mínimo de personas adicionales: cobertura simultánea máxima faltante
            min_needed = self._min_additional_needed(summary)

            # Buscar candidatos internos (empleados con fallback roles)
            candidates: List[str] = []
            if emps and self._role_fallbacks:
                candidates = self._find_training_candidates(ws_name, emps)

            # Razón explicativa
            if summary.primary_deficit_type == DeficitType.STRUCTURAL_NO_SKILL:
                reason = (
                    f"Ningún empleado tiene el skill de {ws_name}. "
                    f"Pool actual: {summary.qualified_pool_size}. "
                    "Se necesita contratación o capacitación urgente."
                )
            else:  # TOO_FEW_QUALIFIED
                reason = (
                    f"El pool de {ws_name} es demasiado pequeño "
                    f"({summary.qualified_pool_size} empleado(s)). "
                    f"Un solo empleado de baja/ausencia genera hueco estructural. "
                    f"Se recomienda al menos {summary.qualified_pool_size + min_needed} en el pool."
                )

            # Estimación de ganancia de cobertura
            gain_estimate = _estimate_coverage_gain(summary, min_needed)

            recs.append(
                TrainingRecommendation(
                    workstation_id=ws_id,
                    workstation_name=ws_name,
                    minimum_additional_people_needed=min_needed,
                    suggested_employees_to_train=[str(c) for c in candidates[:5]],
                    reason=reason,
                    expected_coverage_gain_estimate=gain_estimate,
                )
            )

        recs.sort(key=lambda r: -r.minimum_additional_people_needed)
        return recs

    # ─── REPORTE EJECUTIVO ────────────────────────────────────────────────────

    def to_report_dict(
        self,
        summaries: List[SkillCoverageSummary],
        recommendations: Optional[List[TrainingRecommendation]] = None,
    ) -> Dict[str, Any]:
        """
        Genera un reporte ejecutivo completo con todas las secciones.

        Secciones del reporte:
            global_summary          — KPIs globales (cobertura, huecos, severidades)
            workstations_ranking    — Ranking de ws por déficit (peor primero)
            top_deficit_causes      — Top causas de huecos a nivel global
            structural_gaps         — Huecos NO atacables por algoritmo
            algorithmic_gaps        — Huecos SÍ atacables por algoritmo
            training_recommendations — Recomendaciones de capacitación
            hiring_recommendations  — Ws que requieren contratación externa
            recurrent_patterns      — Patrones de huecos repetidos
        """
        recs = recommendations or []

        # ── Global summary ──
        total_req = sum(s.total_required_slots for s in summaries)
        total_cov = sum(s.total_covered_slots for s in summaries)
        total_miss = sum(s.total_missing_slots for s in summaries)
        global_pct = (total_cov / max(1, total_req + total_miss)) * 100.0 if (total_req + total_miss) > 0 else 100.0

        sev_counts = {s.value: 0 for s in Severity}
        deficit_counts: Dict[str, int] = defaultdict(int)
        for s in summaries:
            sev_counts[s.severity.value] += 1
            deficit_counts[s.primary_deficit_type.value] += 1

        global_summary = {
            "total_workstations_with_gaps": len(summaries),
            "total_missing_slots": total_miss,
            "global_coverage_pct": round(global_pct, 1),
            "severity_counts": sev_counts,
            "structural_ws_count": sum(1 for s in summaries if s.structural_deficit),
            "algorithmic_ws_count": sum(1 for s in summaries if not s.structural_deficit),
        }

        # ── Ranking ──
        ranking = [
            {
                "workstation_name": s.workstation_name,
                "coverage_pct": round(s.coverage_pct, 1),
                "missing_slots": s.total_missing_slots,
                "severity": s.severity.value,
                "deficit_type": s.primary_deficit_type.value,
                "pool_size": s.qualified_pool_size,
            }
            for s in summaries  # ya ordenado peor primero
        ]

        # ── Causas principales ──
        all_gaps = [g for s in summaries for g in s.gaps]
        cause_counts: Dict[str, int] = defaultdict(int)
        for g in all_gaps:
            cause_counts[g.deficit_type.value] += 1
        top_causes = sorted(cause_counts.items(), key=lambda x: -x[1])

        # ── Huecos estructurales (no atacables) ──
        structural_gaps = [g.to_dict() for s in summaries if s.structural_deficit for g in s.gaps]

        # ── Huecos algorítmicos (atacables) ──
        algorithmic_gaps = [
            g.to_dict()
            for s in summaries
            if not s.structural_deficit
            for g in s.gaps
            if g.deficit_type == DeficitType.ALGORITHMIC_GAP
        ]

        # ── Patrones recurrentes ──
        gaps_by_ws = {s.workstation_id: s.gaps for s in summaries}
        recurrent = self.detect_recurrent_gaps(gaps_by_ws)
        recurrent_patterns = [
            {
                "pattern_key": k,
                "occurrences": len(v),
                "workstation": v[0].workstation_name if v else "?",
                "dow": _DOW_NAMES[v[0].dow] if v else "?",
                "time_range": f"{v[0].start_time.strftime('%H:%M')}-{v[0].end_time.strftime('%H:%M')}" if v else "?",
            }
            for k, v in sorted(recurrent.items(), key=lambda x: -len(x[1]))
        ]

        # ── Recomendaciones separadas en capacitación vs contratación ──
        training_recs = [r.to_dict() for r in recs if r.suggested_employees_to_train]
        hiring_recs = [r.to_dict() for r in recs if not r.suggested_employees_to_train]

        return {
            "global_summary": global_summary,
            "workstations_ranking": ranking,
            "top_deficit_causes": [{"cause": c, "count": n} for c, n in top_causes],
            "structural_gaps": structural_gaps,
            "algorithmic_gaps": algorithmic_gaps,
            "training_recommendations": training_recs,
            "hiring_recommendations": hiring_recs,
            "recurrent_patterns": recurrent_patterns,
        }

    # ─── MÉTODOS PRIVADOS ─────────────────────────────────────────────────────

    def _analyze_gap(
        self,
        dm: Any,
        missing_staff: int,
        qualified_emps: List[Any],
        estados: Dict[str, EstadoEmpleado],
        all_emps: List[Any],
        ws_id: str,
    ) -> SkillCoverageGap:
        """Analiza un slot de demanda sin cubrir y devuelve un SkillCoverageGap."""
        d = dm.date
        s_t = getattr(dm, "start", getattr(dm, "start_time", None))
        e_t = getattr(dm, "end", getattr(dm, "end_time", None))
        need = getattr(dm, "need", getattr(dm, "required_staff", 1))
        covered = need - missing_staff
        ws_name = getattr(dm, "wsname", getattr(dm, "workstation_name", ws_id))

        dm_adapted = _DemandAdapter(dm)

        blocked_hours = blocked_window = blocked_day_off = blocked_absence = 0
        available_count = 0

        for emp in qualified_emps:
            key = str(emp.id)
            estado = estados.get(key)

            if emp.absent_day(d):
                blocked_absence += 1
                continue
            if emp.off(d):
                blocked_day_off += 1
                continue

            # Verificar disponibilidad de ventana
            ok, reason = self._validador.puede_asignar(emp, dm_adapted, d, estado or self._empty_estado(emp, d))
            if ok:
                available_count += 1
            elif reason in _HOURS_REASONS:
                blocked_hours += 1
            elif reason in _WINDOW_REASONS:
                blocked_window += 1
            else:
                # Otro motivo (solapamiento, etc.)
                blocked_window += 1

        unavail = blocked_window + blocked_day_off + blocked_absence

        deficit_type = self.classify_deficit(
            qualified_pool_size=len(qualified_emps),
            blocked_by_hours=blocked_hours,
            blocked_by_window=blocked_window,
            blocked_by_day_off=blocked_day_off,
            blocked_by_absence=blocked_absence,
            available_qualified=available_count,
            missing_staff=missing_staff,
        )

        # Severidad del gap individual
        gap_coverage_pct = (covered / max(1, need)) * 100.0
        sev = _compute_severity(
            gap_coverage_pct,
            len(qualified_emps),
            recurrent=False,  # se calcula en el contexto de la ws completa
            is_critical_ws=(len(qualified_emps) == 0),
        )

        duration = _seg_min(s_t, e_t) if s_t and e_t else 0
        return SkillCoverageGap(
            workstation_id=ws_id,
            workstation_name=ws_name,
            date=d,
            dow=d.weekday(),
            start_time=s_t,
            end_time=e_t,
            required_staff=need,
            covered_staff=covered,
            missing_staff=missing_staff,
            qualified_employees_count=len(qualified_emps),
            available_qualified_count=available_count,
            unavailable_qualified_count=unavail,
            blocked_by_hours_count=blocked_hours,
            blocked_by_window_count=blocked_window,
            blocked_by_day_off_count=blocked_day_off,
            blocked_by_absence_count=blocked_absence,
            deficit_type=deficit_type,
            severity=sev,
            demand_id=getattr(dm, "id", None),
        )

    def _primary_deficit_type(self, gaps: List[SkillCoverageGap], qualified_pool: List[Any]) -> DeficitType:
        """
        Determina el tipo de déficit dominante para una workstation.
        Usa el tipo con más ocurrencias; en empate, el más grave.
        """
        if not gaps:
            return DeficitType.DATA_QUALITY_GAP
        counts: Dict[DeficitType, int] = defaultdict(int)
        for g in gaps:
            counts[g.deficit_type] += 1
        # Prioridad en caso de empate: STRUCTURAL > HOURS > AVAILABILITY > ALGORITHMIC
        priority = {
            DeficitType.STRUCTURAL_NO_SKILL: 5,
            DeficitType.STRUCTURAL_TOO_FEW_QUALIFIED: 4,
            DeficitType.HOURS_LIMIT_GAP: 3,
            DeficitType.AVAILABILITY_GAP: 2,
            DeficitType.ALGORITHMIC_GAP: 1,
            DeficitType.DATA_QUALITY_GAP: 0,
        }
        return max(counts, key=lambda t: (counts[t], priority[t]))

    def _detect_recurrent_keys(self, all_gaps: Dict[str, List[SkillCoverageGap]]) -> Set[str]:
        """Retorna el conjunto de claves de patrones recurrentes."""
        recurrent = self.detect_recurrent_gaps(all_gaps)
        return set(recurrent.keys())

    def _min_additional_needed(self, summary: SkillCoverageSummary) -> int:
        """
        Calcula el mínimo de personas adicionales con el skill para cubrir
        el pico de demanda simultánea. Aproximación conservadora:
        si el pool actual es 0 → necesita al menos 1.
        Si > 0 → necesita al menos ceil(missing / pool) personas adicionales.
        """
        if summary.qualified_pool_size == 0:
            # Sin pool: necesitamos al menos 1 per cada franja con distinto horario
            unique_slots = len({(g.start_time, g.end_time) for g in summary.gaps})
            return max(1, min(unique_slots, 3))  # cota pragmática
        # Con pool pequeño: necesitamos subir el pool hasta cubrir el pico
        peak_missing = max((g.missing_staff for g in summary.gaps), default=1)
        return max(
            1, peak_missing - summary.qualified_pool_size + 1 if peak_missing > summary.qualified_pool_size else 1
        )

    def _find_training_candidates(self, ws_name: str, emps: List[Any]) -> List[str]:
        """
        Busca empleados que tienen roles de fallback del ws_name dado
        y por lo tanto podrían capacitarse para cubrirlo.
        """
        fallback_roles = self._role_fallbacks.get(ws_name, [])
        if not fallback_roles:
            return []
        candidates = []
        for emp in emps:
            emp_roles = getattr(emp, "roles", set()) or set()
            for fr in fallback_roles:
                if fr in emp_roles or str(fr) in {str(r) for r in emp_roles}:
                    candidates.append(getattr(emp, "name", str(emp.id)))
                    break
        return candidates

    def _empty_estado(self, emp: Any, d: date) -> EstadoEmpleado:
        """
        Crea un EstadoEmpleado vacío para empleados sin asignaciones.
        Usado cuando un empleado no aparece en el horario generado.
        """
        return EstadoEmpleado(emp_id=str(emp.id))

    def _can(self, emp: Any, ws_id: str) -> bool:
        """Comprueba si el empleado puede trabajar en el ws_id dado."""
        if hasattr(emp, "can"):
            return emp.can(ws_id)
        return ws_id in getattr(emp, "roles", set())


# ─────────────────────────────────────────────────────────────────────────────
# HELPERS PRIVADOS DE MÓDULO
# ─────────────────────────────────────────────────────────────────────────────


def _gap_recurrent_key(g: SkillCoverageGap) -> str:
    """
    Clave de agrupación para detectar patrones recurrentes.
    Bucketiza el horario en bloques de 30 minutos.
    """
    s_m = _t2m(g.start_time) if g.start_time else 0
    bucket = (s_m // 30) * 30  # redondear a bloque de 30 min
    return f"{g.workstation_id}|{g.dow}|{bucket}"


def _worst_days(gaps: List[SkillCoverageGap], top_n: int = 3) -> List[str]:
    """Retorna las fechas ISO con mayor personal faltante."""
    day_miss: Dict[date, int] = defaultdict(int)
    for g in gaps:
        day_miss[g.date] += g.missing_staff
    return [d.isoformat() for d, _ in sorted(day_miss.items(), key=lambda x: -x[1])[:top_n]]


def _worst_time_ranges(gaps: List[SkillCoverageGap], top_n: int = 3) -> List[str]:
    """Retorna los rangos horarios con mayor personal faltante."""
    range_miss: Dict[str, int] = defaultdict(int)
    for g in gaps:
        if g.start_time and g.end_time:
            key = f"{g.start_time.strftime('%H:%M')}-{g.end_time.strftime('%H:%M')}"
            range_miss[key] += g.missing_staff
    return [r for r, _ in sorted(range_miss.items(), key=lambda x: -x[1])[:top_n]]


def _estimate_coverage_gain(summary: SkillCoverageSummary, additional_people: int) -> float:
    """
    Estimación simple de la ganancia de cobertura si se añaden
    `additional_people` personas al pool de la ws.

    Asume linealidad (conservador): cada persona adicional puede cubrir
    max_horas_dia × días_trabajo turnos por semana.
    """
    if summary.total_required_slots == 0:
        return 0.0
    # Estimación: persona adicional puede cubrir ~5 turnos/semana
    slots_per_person = 5
    gain_slots = min(additional_people * slots_per_person, summary.total_missing_slots)
    return round((gain_slots / summary.total_required_slots) * 100.0, 1)
