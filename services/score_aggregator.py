# services/score_aggregator.py
"""
ScheduleScoreAggregator — Gandarias v5.0
=========================================
Calcula el score GLOBAL del horario completo generado por AIScheduleGenerator.

Complementa a TurnQualityService (que puntúa turno a turno) con una visión
agregada que incluye equidad, cobertura global, violaciones y turnos partidos.

Diseño:
- Stateless: recibe todos los datos como parámetros, no guarda estado.
- Determinista: la misma entrada siempre produce la misma salida.
- No requiere conexión a BD.
- Reutilizable antes y después del RepairEngine para medir mejoras.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from datetime import date, time
from typing import Any, Dict, List, Optional, Tuple

from services.ai_scheduler import (
    EstadoEmpleado,
    _end_min,
    _merge_intervals,
    _t2m,
)

# ─────────────────────────────────────────────────────────────────────────────
# PESOS POR DEFECTO
# ─────────────────────────────────────────────────────────────────────────────

DEFAULT_WEIGHTS = {
    "coverage": 0.55,  # Métrica principal: % de demanda cubierta
    "fairness": 0.20,  # Equidad de distribución de carga
    "rules": 0.25,  # Cumplimiento de restricciones
}

# Penalización por violación dura (sobre el rules_score)
HARD_VIOLATION_PENALTY = 15.0
# Penalización por violación blanda
SOFT_VIOLATION_PENALTY = 2.0
# Umbral bajo el cual el score total se penaliza fuertemente
HARD_VIOLATION_TOTAL_PENALTY = 20.0


# ─────────────────────────────────────────────────────────────────────────────
# DTO: SCHEDULE SCORE
# ─────────────────────────────────────────────────────────────────────────────


@dataclass
class ScheduleScore:
    """
    Score global de un horario generado.

    Campos de score (0-100):
        total_score        — Score compuesto final
        coverage_score     — Subpuntaje de cobertura de demanda
        fairness_score     — Subpuntaje de equidad de carga entre empleados
        rules_score        — Subpuntaje de cumplimiento de restricciones
        preference_score   — Placeholder (siempre 100.0 en v1, sin datos de preferencias)

    Métricas brutas:
        coverage_pct           — % de slots cubiertos
        covered_slots          — Slots cubiertos (sum coverage_stats.covered)
        total_slots            — Slots requeridos (sum demand.need)
        critical_gaps          — Huecos inevitables (clasificados por GapClassifier)
        fixable_gaps           — Huecos corregibles
        structural_gaps        — Huecos sin clasificar
        violations_hard        — Violaciones de restricciones duras
        violations_soft        — Violaciones de restricciones blandas
        split_shifts_count     — Número de días con turno partido por empleado
        employees_assigned     — Empleados con al menos un turno
        employees_unassigned   — Empleados activos sin ningún turno
        repair_delta           — Diferencia de score respecto a versión anterior (0.0 si es el original)
    """

    total_score: float = 0.0
    coverage_score: float = 0.0
    fairness_score: float = 0.0
    rules_score: float = 100.0
    preference_score: float = 100.0

    coverage_pct: float = 0.0
    covered_slots: int = 0
    total_slots: int = 0

    critical_gaps: int = 0
    fixable_gaps: int = 0
    structural_gaps: int = 0

    violations_hard: int = 0
    violations_soft: int = 0

    split_shifts_count: int = 0
    employees_assigned: int = 0
    employees_unassigned: int = 0

    repair_delta: float = 0.0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "total_score": round(self.total_score, 2),
            "coverage_score": round(self.coverage_score, 2),
            "fairness_score": round(self.fairness_score, 2),
            "rules_score": round(self.rules_score, 2),
            "preference_score": round(self.preference_score, 2),
            "coverage_pct": round(self.coverage_pct, 2),
            "covered_slots": self.covered_slots,
            "total_slots": self.total_slots,
            "critical_gaps": self.critical_gaps,
            "fixable_gaps": self.fixable_gaps,
            "structural_gaps": self.structural_gaps,
            "violations_hard": self.violations_hard,
            "violations_soft": self.violations_soft,
            "split_shifts_count": self.split_shifts_count,
            "employees_assigned": self.employees_assigned,
            "employees_unassigned": self.employees_unassigned,
            "repair_delta": round(self.repair_delta, 2),
        }


# ─────────────────────────────────────────────────────────────────────────────
# AGGREGATOR
# ─────────────────────────────────────────────────────────────────────────────


class ScheduleScoreAggregator:
    """
    Evalúa la calidad global de un horario.

    Uso básico:
        aggregator = ScheduleScoreAggregator()
        score = aggregator.aggregate(sched, demands, emps, coverage_stats)

    Uso con estados pre-calculados (más rápido):
        score = aggregator.aggregate(sched, demands, emps, coverage_stats, estados=estados)

    Uso con metadatos de reparación:
        score = aggregator.aggregate(..., violations_hard=n, gap_counts={"critical": k, "fixable": m})
    """

    def __init__(self, weights: Optional[Dict[str, float]] = None):
        w = weights or DEFAULT_WEIGHTS
        total = sum(w.values())
        # Normalizar por si los pesos no suman 1.0
        self._w_coverage = w.get("coverage", 0.55) / total
        self._w_fairness = w.get("fairness", 0.20) / total
        self._w_rules = w.get("rules", 0.25) / total

    # ─────────────────────────────────────── API PRINCIPAL ──────────────────

    def aggregate(
        self,
        sched: Dict[date, List[Tuple]],
        demands: List,
        emps: List,
        coverage_stats: Dict[Any, Dict],
        violations_hard: int = 0,
        violations_soft: int = 0,
        gap_counts: Optional[Dict[str, int]] = None,
        estados: Optional[Dict[str, EstadoEmpleado]] = None,
    ) -> ScheduleScore:
        """
        Calcula el ScheduleScore completo.

        Parámetros:
            sched            — Horario generado: {date: [(Emp, Demand)]}
            demands          — Lista completa de demandas originales
            emps             — Lista de empleados
            coverage_stats   — Diccionario de cobertura por demand_id
            violations_hard  — Número de violaciones de restricciones duras
            violations_soft  — Número de violaciones blandas
            gap_counts       — Dict opcional con {"critical": n, "fixable": m, "structural": k}
            estados          — Dict[emp_id_str, EstadoEmpleado] pre-calculado (opcional)
        """
        if estados is None:
            estados = self._reconstruct_estados(emps, sched)

        covered, total = self.calculate_coverage(coverage_stats)
        coverage_pct = (covered / total * 100.0) if total > 0 else 100.0
        coverage_score = coverage_pct  # ya está en 0-100

        fairness_score = self.calculate_fairness(emps, estados)
        rules_score = self.calculate_rules_score(violations_hard, violations_soft)
        split_count = self.calculate_split_shifts(estados)
        assigned, unassigned = self._count_assignment_status(emps, estados)

        total_score = self.calculate_total_score(coverage_score, fairness_score, rules_score, violations_hard)

        gc = gap_counts or {}
        return ScheduleScore(
            total_score=total_score,
            coverage_score=round(coverage_score, 2),
            fairness_score=round(fairness_score, 2),
            rules_score=round(rules_score, 2),
            preference_score=100.0,
            coverage_pct=round(coverage_pct, 2),
            covered_slots=covered,
            total_slots=total,
            critical_gaps=gc.get("critical", 0),
            fixable_gaps=gc.get("fixable", 0),
            structural_gaps=gc.get("structural", 0),
            violations_hard=violations_hard,
            violations_soft=violations_soft,
            split_shifts_count=split_count,
            employees_assigned=assigned,
            employees_unassigned=unassigned,
            repair_delta=0.0,
        )

    # ─────────────────────────────────────── SUBMÉTODOS PÚBLICOS ────────────

    def calculate_coverage(self, coverage_stats: Dict[Any, Dict]) -> Tuple[int, int]:
        """
        Retorna (covered_slots, total_slots) desde coverage_stats.

        covered_slots = suma de cs["covered"] para todas las demandas
        total_slots   = suma de cs["demand"].need para todas las demandas
        """
        covered = sum(cs.get("covered", 0) for cs in coverage_stats.values())
        total = sum(cs["demand"].need for cs in coverage_stats.values() if "demand" in cs)
        return covered, total

    def calculate_fairness(self, emps: List, estados: Dict[str, EstadoEmpleado]) -> float:
        """
        Mide equidad de carga semanal entre empleados activos.

        Métrica: 1 - CV (coeficiente de variación) de horas asignadas.
        CV = desviación_estándar / media

        score = 100 * max(0, 1 - CV)
        - CV = 0   → score = 100 (distribución perfecta)
        - CV = 0.5 → score = 50
        - CV ≥ 1.0 → score = 0
        """
        hours = []
        for e in emps:
            est = estados.get(str(e.id))
            if est is None:
                continue
            # Solo contar empleados que podrían trabajar (no todos los días libres)
            # Si tiene asignaciones o podría tener, incluir
            h = est.minutos_semana / 60.0
            hours.append(h)

        if not hours:
            return 100.0

        working = [h for h in hours if h > 0]
        if len(working) < 2:
            # 0 o 1 empleado trabajando — no hay distribución que evaluar
            return 100.0 if working else 0.0

        mean = sum(working) / len(working)
        if mean <= 0:
            return 100.0

        variance = sum((h - mean) ** 2 for h in working) / len(working)
        std = math.sqrt(variance)
        cv = std / mean

        fairness = max(0.0, 1.0 - cv) * 100.0
        return round(fairness, 2)

    def calculate_rules_score(self, violations_hard: int, violations_soft: int) -> float:
        """
        Score de cumplimiento de restricciones (0-100).

        Penalización:
        - Por cada violación dura: -HARD_VIOLATION_PENALTY puntos
        - Por cada violación blanda: -SOFT_VIOLATION_PENALTY puntos

        Resultado: max(0, 100 - penalizaciones)
        """
        penalty = violations_hard * HARD_VIOLATION_PENALTY + violations_soft * SOFT_VIOLATION_PENALTY
        return max(0.0, round(100.0 - penalty, 2))

    def calculate_split_shifts(self, estados: Dict[str, EstadoEmpleado]) -> int:
        """
        Cuenta el número de (empleado × día) con turno partido.

        Un turno es partido si el empleado tiene 2 bloques no-contiguos
        en el mismo día (hay un gap entre intervalos merged).
        """
        count = 0
        for est in estados.values():
            for d, ivs in est.intervalos_por_dia.items():
                if len(ivs) < 2:
                    continue
                merged = _merge_intervals(list(ivs))
                if len(merged) >= 2:
                    count += 1
        return count

    def calculate_total_score(
        self,
        coverage_score: float,
        fairness_score: float,
        rules_score: float,
        violations_hard: int = 0,
    ) -> float:
        """
        Combina los sub-scores en un score total (0-100).

        Si hay violaciones duras, se aplica penalización adicional al total.
        """
        raw = self._w_coverage * coverage_score + self._w_fairness * fairness_score + self._w_rules * rules_score
        # Penalización adicional por violaciones duras: cae el score total
        if violations_hard > 0:
            raw = max(0.0, raw - violations_hard * HARD_VIOLATION_TOTAL_PENALTY)

        return round(max(0.0, min(100.0, raw)), 2)

    # ─────────────────────────────────────── HELPERS ────────────────────────

    def _reconstruct_estados(self, emps: List, sched: Dict[date, List[Tuple]]) -> Dict[str, EstadoEmpleado]:
        """
        Reconstruye los EstadoEmpleado desde el horario generado.

        Necesario porque AIScheduleGenerator.generar() no retorna los estados.
        """
        estados: Dict[str, EstadoEmpleado] = {str(e.id): EstadoEmpleado(emp_id=str(e.id)) for e in emps}
        for d, assigns in sched.items():
            for emp, dm in assigns:
                ws_id = getattr(dm, "wsid", None)
                if ws_id is None:
                    continue
                s_min = _t2m(dm.start)
                e_min = _end_min(dm.end)
                emp_key = str(emp.id)
                if emp_key in estados:
                    estados[emp_key].registrar(d, str(ws_id), s_min, e_min)
        return estados

    def _count_assignment_status(self, emps: List, estados: Dict[str, EstadoEmpleado]) -> Tuple[int, int]:
        """Retorna (empleados_con_turno, empleados_sin_turno)."""
        assigned = 0
        unassigned = 0
        for e in emps:
            est = estados.get(str(e.id))
            if est and est.minutos_semana > 0:
                assigned += 1
            else:
                unassigned += 1
        return assigned, unassigned

    def score_delta(self, before: ScheduleScore, after: ScheduleScore) -> ScheduleScore:
        """
        Retorna 'after' con repair_delta calculado respecto a 'before'.
        No modifica 'before'.
        """
        import copy

        result = copy.copy(after)
        result.repair_delta = round(after.total_score - before.total_score, 2)
        return result
