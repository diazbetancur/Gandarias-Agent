# services/repair_engine.py
"""
ScheduleRepairEngine — Gandarias v5.0
=======================================
Intenta mejorar el horario generado por AIScheduleGenerator cubriendo
huecos corregibles mediante swaps, extensiones de turno y fallbacks de rol.

Principios de diseño:
- Trabaja DESPUÉS de AIScheduleGenerator.generar(). No modifica el generador.
- Cada reparación se valida con ValidadorReglasDuras.puede_asignar() antes de aplicar.
- Si el score global no mejora tras una reparación, se revierte completamente.
- Todos los cambios son auditables: se registra cada intento en RepairSuggestion.
- Las restricciones duras NUNCA se relajan.
- Límite de gaps y candidatos por gap para evitar explosión combinatoria.

Flujo principal:
    engine = ScheduleRepairEngine(emps, demands, validador, scorer, reglas)
    result = engine.reparar(sched, coverage_stats)
    # result.repaired_score.coverage_pct > result.original_score.coverage_pct
"""

from __future__ import annotations

import copy
import logging
import time as time_module
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import date, time
from enum import Enum
from typing import Any, Dict, List, Optional, Set, Tuple

from services.ai_scheduler import (
    EstadoEmpleado,
    ScorerCandidatos,
    ValidadorReglasDuras,
    _end_min,
    _seg_min,
    _t2m,
    REGLAS_DURAS_DEFAULTS,
)
from services.score_aggregator import ScheduleScore, ScheduleScoreAggregator
from services.gap_classifier import (
    ClassifiedGap,
    GapType,
    ScheduleGapClassifier,
    _GapDemandAdapter,
)

logger = logging.getLogger("repair_engine")


# ─────────────────────────────────────────────────────────────────────────────
# ENUMS Y DTOs
# ─────────────────────────────────────────────────────────────────────────────


class RepairType(str, Enum):
    DIRECT = "DIRECT"  # Asignación directa (el generador lo pasó por alto)
    SWAP = "SWAP"  # Intercambio de turno entre empleados
    EXTENSION = "EXTENSION"  # Extensión de turno existente
    FALLBACK = "FALLBACK"  # Uso de rol de fallback


@dataclass
class RepairSuggestion:
    """
    Registro de un intento de reparación (aplicado o rechazado).

    gap_demand_id           — ID de la demanda que se intentó cubrir
    repair_type             — Tipo de reparación intentada
    description             — Descripción legible de la operación
    target_employee_id      — Empleado que cubriría el hueco
    displaced_assignment    — Tupla (date, ws_id, s_min, e_min) de la asignación movida (si SWAP)
    replacement_employee_id — Empleado que tomó la asignación desplazada (si SWAP)
    score_delta             — Diferencia de covered_slots antes/después (positivo = mejora)
    applied                 — True si la reparación fue aplicada y conservada
    not_applied_reason      — Razón de rechazo si no se aplicó
    """

    gap_demand_id: Any
    repair_type: RepairType
    description: str
    target_employee_id: str
    displaced_assignment: Optional[Tuple] = None
    replacement_employee_id: Optional[str] = None
    score_delta: float = 0.0
    applied: bool = False
    not_applied_reason: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "gap_demand_id": str(self.gap_demand_id),
            "repair_type": self.repair_type.value,
            "description": self.description,
            "target_employee_id": self.target_employee_id,
            "displaced_assignment": (
                [
                    str(self.displaced_assignment[0]),
                    self.displaced_assignment[1],
                    self.displaced_assignment[2],
                    self.displaced_assignment[3],
                ]
                if self.displaced_assignment
                else None
            ),
            "replacement_employee_id": self.replacement_employee_id,
            "score_delta": round(self.score_delta, 4),
            "applied": self.applied,
            "not_applied_reason": self.not_applied_reason,
        }


@dataclass
class OptimizationResult:
    """
    Resultado completo de la fase de reparación.

    original_score      — Score antes de aplicar cualquier reparación
    repaired_score      — Score después de todas las reparaciones aplicadas
    gaps_before         — Número de huecos (demands con unmet > 0) al inicio
    gaps_after          — Número de huecos al finalizar
    repairs_attempted   — Total de reparaciones intentadas
    repairs_applied     — Reparaciones que mejoraron el horario y se conservaron
    repair_suggestions  — Lista completa de intentos (aplicados y rechazados)
    execution_time_ms   — Tiempo total de la fase de reparación en ms
    solver_used         — Siempre False en esta versión (sin OR-Tools)
    solver_name         — Siempre None en esta versión
    solver_objective_value — Siempre None en esta versión
    """

    original_score: ScheduleScore
    repaired_score: ScheduleScore
    gaps_before: int = 0
    gaps_after: int = 0
    repairs_attempted: int = 0
    repairs_applied: int = 0
    repair_suggestions: List[RepairSuggestion] = field(default_factory=list)
    execution_time_ms: int = 0
    solver_used: bool = False
    solver_name: Optional[str] = None
    solver_objective_value: Optional[float] = None

    @property
    def coverage_improvement(self) -> float:
        """Mejora de cobertura en puntos porcentuales."""
        return round(self.repaired_score.coverage_pct - self.original_score.coverage_pct, 2)

    @property
    def repair_success_rate(self) -> float:
        """Tasa de éxito de reparaciones (0.0–1.0)."""
        if self.repairs_attempted == 0:
            return 0.0
        return round(self.repairs_applied / self.repairs_attempted, 4)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "original_score": self.original_score.to_dict(),
            "repaired_score": self.repaired_score.to_dict(),
            "gaps_before": self.gaps_before,
            "gaps_after": self.gaps_after,
            "repairs_attempted": self.repairs_attempted,
            "repairs_applied": self.repairs_applied,
            "repair_success_rate": self.repair_success_rate,
            "coverage_improvement": self.coverage_improvement,
            "execution_time_ms": self.execution_time_ms,
            "solver_used": self.solver_used,
            "repair_suggestions": [s.to_dict() for s in self.repair_suggestions],
        }


# ─────────────────────────────────────────────────────────────────────────────
# DEMAND ADAPTER PARA GAPS
# ─────────────────────────────────────────────────────────────────────────────


class _AssignmentDemandAdapter:
    """
    Adaptador mínimo para usar una tupla de asignación existente
    como demand en ValidadorReglasDuras.puede_asignar().
    """

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
    )

    def __init__(self, d: date, wsid: Any, wsname: str, start: time, end: time):
        self.id = f"_REPAIR_{wsid}_{d}"
        self.date = d
        self.wsid = wsid
        self.wsname = wsname
        self.start = start
        self.end = end
        self.need = 1
        self.raw_need = 1.0
        self.has_hybrid_component = False
        self.observation_override = None


# ─────────────────────────────────────────────────────────────────────────────
# REPAIR ENGINE
# ─────────────────────────────────────────────────────────────────────────────


class ScheduleRepairEngine:
    """
    Motor de reparación post-generación.

    Uso después de AIScheduleGenerator.generar():

        sched, coverage_stats, diag = generator.generar(emps, demands, week)

        engine = ScheduleRepairEngine(
            emps=emps,
            demands=demands,
            validador=generator.validador,
            scorer=generator.scorer,
            reglas=reglas,
            overrides=overrides,
        )
        result = engine.reparar(sched, coverage_stats)

        print(f"Cobertura: {result.original_score.coverage_pct}% → "
              f"{result.repaired_score.coverage_pct}%")
    """

    def __init__(
        self,
        emps: List,
        demands: List,
        validador: Optional[ValidadorReglasDuras] = None,
        scorer: Optional[ScorerCandidatos] = None,
        reglas: Optional[Dict] = None,
        overrides: Optional[Set] = None,
        role_fallbacks: Optional[Dict[str, List[str]]] = None,
        max_gaps: int = 20,
        max_candidates_per_gap: int = 10,
        debug: bool = True,
    ):
        """
        Parámetros:
            emps                  — Lista de empleados (Emp)
            demands               — Lista completa de demandas originales
            validador             — ValidadorReglasDuras (compartir con el generador)
            scorer                — ScorerCandidatos (compartir con el generador)
            reglas                — Reglas duras; si es None usa REGLAS_DURAS_DEFAULTS
            overrides             — Set de (emp_id_str, date) que saltan UserShift
            role_fallbacks        — Mapa de nombre_ws → [nombre_ws_fallback, ...]
            max_gaps              — Máximo de huecos a intentar reparar (evita O(n²))
            max_candidates_per_gap— Máximo de candidatos evaluados por hueco
            debug                 — Activar logging detallado
        """
        _reglas = reglas or dict(REGLAS_DURAS_DEFAULTS)
        self.emps = emps
        self.demands = demands
        self.validador = validador or ValidadorReglasDuras(_reglas)
        self.scorer = scorer
        self.reglas = _reglas
        self.overrides = overrides or set()
        self.role_fallbacks = role_fallbacks or {}
        self.max_gaps = max_gaps
        self.max_candidates_per_gap = max_candidates_per_gap
        self.debug = debug

        self._aggregator = ScheduleScoreAggregator()
        self._classifier = ScheduleGapClassifier(
            emps=emps,
            validador=self.validador,
            reglas=_reglas,
            role_fallbacks=self.role_fallbacks,
            debug=debug,
        )

        # Mapa demand_id → Demand para búsquedas rápidas
        self._demands_by_id: Dict[Any, Any] = {dm.id: dm for dm in demands}
        # Mapa (date, wsid_str, s_min, e_min) → Demand para búsqueda por asignación
        self._demands_by_slot: Dict[Tuple, List[Any]] = defaultdict(list)
        for dm in demands:
            key = (dm.date, str(dm.wsid), _t2m(dm.start), _end_min(dm.end))
            self._demands_by_slot[key].append(dm)

    def _log(self, msg: str) -> None:
        if self.debug:
            logger.debug(msg)

    # ─────────────────────────────────────────── API PRINCIPAL ──────────────

    def reparar(
        self,
        sched: Dict[date, List[Tuple]],
        coverage_stats: Dict[Any, Dict],
    ) -> OptimizationResult:
        """
        Intenta reparar el horario generado.

        Modifica sched y coverage_stats IN-PLACE cuando mejora.
        Si no mejora, revierte cada cambio individualmente.

        Retorna OptimizationResult con métricas completas.
        """
        t_start = time_module.time()
        self._log("══ REPAIR ENGINE — iniciando ══")

        # ── 1. Reconstruir estados desde el sched ─────────────────────────
        estados = self._reconstruct_estados(sched)

        # ── 2. Score inicial ──────────────────────────────────────────────
        score_before = self._aggregator.aggregate(sched, self.demands, self.emps, coverage_stats, estados=estados)
        self._log(
            f"[REPAIR] Score inicial: {score_before.total_score:.1f} | "
            f"Cobertura: {score_before.coverage_pct:.1f}% | "
            f"Huecos: {score_before.total_slots - score_before.covered_slots}"
        )

        # ── 3. Clasificar huecos ──────────────────────────────────────────
        gaps = self._classifier.classify(coverage_stats, sched, estados=estados, overrides=self.overrides)
        gaps_before = len(gaps)
        summary = self._classifier.summarize(gaps)
        self._log(
            f"[REPAIR] Huecos: {gaps_before} total | "
            f"inevitables={summary['inevitable']} | "
            f"corregibles={summary['fixable']}"
        )

        # ── 4. Priorizar huecos corregibles ───────────────────────────────
        fixable = [g for g in gaps if g.is_fixable]
        fixable.sort(key=lambda g: g.criticality_score, reverse=True)
        fixable = fixable[: self.max_gaps]

        # ── 5. Reparar ────────────────────────────────────────────────────
        all_suggestions: List[RepairSuggestion] = []
        repairs_applied = 0
        repairs_attempted = 0
        baseline_covered = score_before.covered_slots

        for gap in fixable:
            # Verificar que el hueco sigue sin cubrir
            cs = coverage_stats.get(gap.demand_id, {})
            if cs.get("unmet", 0) <= 0:
                continue

            self._log(
                f"[REPAIR] Intentando hueco: {gap.workstation_name} "
                f"{gap.date} {gap.start_time}-{gap.end_time} "
                f"tipo={gap.gap_type.value}"
            )

            suggestion = None

            # A) Asignación directa
            repairs_attempted += 1
            suggestion = self._try_direct(gap, sched, estados, coverage_stats)
            if suggestion and suggestion.applied:
                all_suggestions.append(suggestion)
                repairs_applied += 1
                self._log(f"[REPAIR] ✓ DIRECT aplicado para {gap.demand_id}")
                continue

            if suggestion:
                all_suggestions.append(suggestion)

            # B) Swap
            repairs_attempted += 1
            suggestion = self._try_swap(gap, sched, estados, coverage_stats, baseline_covered)
            if suggestion and suggestion.applied:
                all_suggestions.append(suggestion)
                repairs_applied += 1
                baseline_covered = sum(cs2.get("covered", 0) for cs2 in coverage_stats.values())
                self._log(f"[REPAIR] ✓ SWAP aplicado para {gap.demand_id}")
                continue

            if suggestion:
                all_suggestions.append(suggestion)

            # C) Extensión
            repairs_attempted += 1
            suggestion = self._try_extension(gap, sched, estados, coverage_stats, baseline_covered)
            if suggestion and suggestion.applied:
                all_suggestions.append(suggestion)
                repairs_applied += 1
                baseline_covered = sum(cs2.get("covered", 0) for cs2 in coverage_stats.values())
                self._log(f"[REPAIR] ✓ EXTENSION aplicada para {gap.demand_id}")
                continue

            if suggestion:
                all_suggestions.append(suggestion)

            self._log(f"[REPAIR] ✗ No se pudo reparar: {gap.demand_id}")

        # ── 6. Score final ────────────────────────────────────────────────
        score_after = self._aggregator.aggregate(sched, self.demands, self.emps, coverage_stats, estados=estados)
        score_after = self._aggregator.score_delta(score_before, score_after)
        gaps_after = sum(1 for cs in coverage_stats.values() if cs.get("unmet", 0) > 0)

        t_end = time_module.time()
        elapsed_ms = int((t_end - t_start) * 1000)

        self._log(
            f"══ REPAIR ENGINE — fin ══ "
            f"{repairs_applied}/{repairs_attempted} reparaciones | "
            f"huecos {gaps_before}→{gaps_after} | "
            f"cobertura {score_before.coverage_pct:.1f}%→{score_after.coverage_pct:.1f}% | "
            f"{elapsed_ms}ms"
        )

        return OptimizationResult(
            original_score=score_before,
            repaired_score=score_after,
            gaps_before=gaps_before,
            gaps_after=gaps_after,
            repairs_attempted=repairs_attempted,
            repairs_applied=repairs_applied,
            repair_suggestions=all_suggestions,
            execution_time_ms=elapsed_ms,
            solver_used=False,
            solver_name=None,
            solver_objective_value=None,
        )

    # ─────────────────────────────────── ESTRATEGIAS DE REPARACIÓN ──────────

    def _try_direct(
        self,
        gap: ClassifiedGap,
        sched: Dict,
        estados: Dict[str, EstadoEmpleado],
        coverage_stats: Dict,
    ) -> Optional[RepairSuggestion]:
        """
        Intenta asignar directamente un empleado al hueco.
        Solo aplica cuando hay candidatos válidos que el generador pasó por alto.
        """
        gap_dm = _GapDemandAdapter(gap)
        candidates = gap.available_employees  # ya validados en el clasificador

        for emp_id in candidates[: self.max_candidates_per_gap]:
            emp = self._find_emp(emp_id)
            if emp is None:
                continue
            estado = estados[str(emp.id)]
            ok, reason = self.validador.puede_asignar(emp, gap_dm, gap.date, estado, self.overrides)
            if not ok:
                continue

            # Aplicar
            self._apply_assignment(emp, gap_dm, sched, estados, coverage_stats)

            sugg = RepairSuggestion(
                gap_demand_id=gap.demand_id,
                repair_type=RepairType.DIRECT,
                description=(
                    f"Asignación directa: {emp.name} → "
                    f"{gap.workstation_name} {gap.date} "
                    f"{gap.start_time}-{gap.end_time}"
                ),
                target_employee_id=str(emp.id),
                score_delta=1.0,
                applied=True,
            )
            return sugg

        return (
            RepairSuggestion(
                gap_demand_id=gap.demand_id,
                repair_type=RepairType.DIRECT,
                description="Sin candidatos directos disponibles",
                target_employee_id="",
                applied=False,
                not_applied_reason="NO_DIRECT_CANDIDATES",
            )
            if not candidates
            else None
        )

    def _try_swap(
        self,
        gap: ClassifiedGap,
        sched: Dict,
        estados: Dict[str, EstadoEmpleado],
        coverage_stats: Dict,
        baseline_covered: int,
    ) -> Optional[RepairSuggestion]:
        """
        Intenta un intercambio de turno para cubrir el hueco.

        Para cada empleado habilitado con el skill del gap que está saturado:
          1. Busca una asignación existente del empleado que otro pueda tomar.
          2. Simula: quitar asignación del empleado saturado, dársela al reemplazo.
          3. Verifica que el empleado saturado puede ahora cubrir el hueco.
          4. Aplica si la cobertura mejora. Revierte si no.
        """
        gap_dm = _GapDemandAdapter(gap)
        skill_qualified = gap.skill_qualified_employees[: self.max_candidates_per_gap]

        for emp_id in skill_qualified:
            emp = self._find_emp(emp_id)
            if emp is None:
                continue

            estado = estados[str(emp.id)]

            # ¿Puede asignarlo directamente sin swap?
            ok_direct, _ = self.validador.puede_asignar(emp, gap_dm, gap.date, estado, self.overrides)
            if ok_direct:
                # Ya cubierto por DIRECT; swap no necesario
                continue

            # Iterar asignaciones del empleado buscando la que puede ceder
            asignaciones_snap = list(estado.asignaciones)  # snapshot
            for d_assign, ws_assign, s_assign, e_assign in asignaciones_snap:
                # No mover asignaciones híbridas
                if str(ws_assign).startswith("HYB:"):
                    continue

                # Recuperar demand original de esta asignación
                dm_orig = self._find_demand_for_assignment(d_assign, ws_assign, s_assign, e_assign)
                if dm_orig is None:
                    continue

                # Buscar reemplazo para la asignación que vamos a mover
                alt_emp = self._find_replacement(emp, dm_orig, d_assign, sched, estados)
                if alt_emp is None:
                    continue

                # ── Simular intercambio ──────────────────────────────────
                # Paso 1: quitar asignación de emp
                self._remove_assignment(emp, dm_orig, sched, estados, coverage_stats)

                # Paso 2: validar que alt_emp puede tomar la asignación
                ok_alt, reason_alt = self.validador.puede_asignar(
                    alt_emp, dm_orig, d_assign, estados[str(alt_emp.id)], self.overrides
                )
                if not ok_alt:
                    # Revertir paso 1
                    self._apply_assignment(emp, dm_orig, sched, estados, coverage_stats)
                    continue

                # Paso 3: asignar alt_emp a la demanda desplazada
                self._apply_assignment(alt_emp, dm_orig, sched, estados, coverage_stats)

                # Paso 4: verificar que emp ahora puede cubrir el gap
                ok_gap, reason_gap = self.validador.puede_asignar(
                    emp, gap_dm, gap.date, estados[str(emp.id)], self.overrides
                )
                if not ok_gap:
                    # Revertir pasos 3 y 1
                    self._remove_assignment(alt_emp, dm_orig, sched, estados, coverage_stats)
                    self._apply_assignment(emp, dm_orig, sched, estados, coverage_stats)
                    continue

                # Paso 5: asignar emp al gap
                self._apply_assignment(emp, gap_dm, sched, estados, coverage_stats)

                # ── Evaluar mejora ───────────────────────────────────────
                new_covered = sum(cs.get("covered", 0) for cs in coverage_stats.values())
                delta = new_covered - baseline_covered

                if delta > 0:
                    # Mejora real — conservar
                    self._log(
                        f"[SWAP] ✓ {emp.name} cede {ws_assign}/{d_assign} "
                        f"a {alt_emp.name}, cubre gap {gap.workstation_name}"
                    )
                    return RepairSuggestion(
                        gap_demand_id=gap.demand_id,
                        repair_type=RepairType.SWAP,
                        description=(
                            f"Swap: {emp.name} cede turno {d_assign}/{ws_assign} "
                            f"a {alt_emp.name} → {emp.name} cubre "
                            f"{gap.workstation_name} {gap.date}"
                        ),
                        target_employee_id=str(emp.id),
                        displaced_assignment=(d_assign, ws_assign, s_assign, e_assign),
                        replacement_employee_id=str(alt_emp.id),
                        score_delta=float(delta),
                        applied=True,
                    )

                # Sin mejora — revertir todo
                self._remove_assignment(emp, gap_dm, sched, estados, coverage_stats)
                self._remove_assignment(alt_emp, dm_orig, sched, estados, coverage_stats)
                self._apply_assignment(emp, dm_orig, sched, estados, coverage_stats)
                self._log(f"[SWAP] ✗ Swap {emp.name}↔{alt_emp.name} no mejora cobertura " f"(delta={delta}), revertido")

        return RepairSuggestion(
            gap_demand_id=gap.demand_id,
            repair_type=RepairType.SWAP,
            description="Ningún swap encontrado que mejore la cobertura",
            target_employee_id="",
            applied=False,
            not_applied_reason="NO_VALID_SWAP",
        )

    def _try_extension(
        self,
        gap: ClassifiedGap,
        sched: Dict,
        estados: Dict[str, EstadoEmpleado],
        coverage_stats: Dict,
        baseline_covered: int,
    ) -> Optional[RepairSuggestion]:
        """
        Intenta extender el turno de un empleado ya asignado ese día para
        cubrir el hueco, respetando max_horas_dia y descanso.

        Estrategia:
          - Buscar empleados asignados el mismo día con el skill del gap.
          - Crear una demand adapter para la franja del gap.
          - Validar con puede_asignar() (que ya verifica MAX_HORAS_DIA y solapamiento).
          - Aplicar si mejora la cobertura.
        """
        gap_dm = _GapDemandAdapter(gap)
        max_h_min = self.reglas.get("max_horas_por_dia", 9) * 60
        gap_dur = _seg_min(gap.start_time, gap.end_time)
        d = gap.date

        # Empleados asignados hoy con el skill requerido
        candidates_today: List[Any] = []
        for emp_id, est in estados.items():
            if d not in est.dias_trabajados:
                continue
            emp = self._find_emp(emp_id)
            if emp is None or not emp.can(gap.workstation_id):
                continue
            hoy_min = est.minutos_por_dia.get(d, 0)
            if hoy_min + gap_dur <= max_h_min:
                candidates_today.append(emp)

        for emp in candidates_today[: self.max_candidates_per_gap]:
            estado = estados[str(emp.id)]
            ok, reason = self.validador.puede_asignar(emp, gap_dm, gap.date, estado, self.overrides)
            if not ok:
                self._log(f"[EXTENSION] {emp.name} rechazado para extensión: {reason}")
                continue

            # Aplicar extensión
            self._apply_assignment(emp, gap_dm, sched, estados, coverage_stats)

            new_covered = sum(cs.get("covered", 0) for cs in coverage_stats.values())
            delta = new_covered - baseline_covered

            if delta > 0:
                self._log(
                    f"[EXTENSION] ✓ {emp.name} extiende turno para cubrir "
                    f"{gap.workstation_name} {gap.date} {gap.start_time}-{gap.end_time}"
                )
                return RepairSuggestion(
                    gap_demand_id=gap.demand_id,
                    repair_type=RepairType.EXTENSION,
                    description=(
                        f"Extensión: {emp.name} extiende turno del {d} "
                        f"para cubrir {gap.workstation_name} "
                        f"{gap.start_time}-{gap.end_time}"
                    ),
                    target_employee_id=str(emp.id),
                    score_delta=float(delta),
                    applied=True,
                )

            # Sin mejora — revertir
            self._remove_assignment(emp, gap_dm, sched, estados, coverage_stats)
            self._log(f"[EXTENSION] ✗ Extensión {emp.name} no mejora cobertura, revertida")

        return RepairSuggestion(
            gap_demand_id=gap.demand_id,
            repair_type=RepairType.EXTENSION,
            description="Ninguna extensión posible sin violar restricciones",
            target_employee_id="",
            applied=False,
            not_applied_reason="NO_VALID_EXTENSION",
        )

    # ─────────────────────────────────────── HELPERS DE ESTADO ──────────────

    def _apply_assignment(
        self,
        emp: Any,
        dm: Any,
        sched: Dict,
        estados: Dict[str, EstadoEmpleado],
        coverage_stats: Dict,
    ) -> None:
        """Registra una asignación en sched, estados y coverage_stats."""
        d = dm.date
        s_min = _t2m(dm.start)
        e_min = _end_min(dm.end)

        sched.setdefault(d, []).append((emp, dm))
        estados[str(emp.id)].registrar(d, str(dm.wsid), s_min, e_min)

        # Actualizar coverage_stats si existe el demand_id
        dm_id = dm.id
        if dm_id in coverage_stats:
            cs = coverage_stats[dm_id]
            cs["covered"] = cs.get("covered", 0) + 1
            cs["met"] = cs.get("met", 0) + 1
            cs["unmet"] = max(0, cs.get("unmet", 0) - 1)
            employees_list = cs.setdefault("employees", [])
            employees_list.append(str(emp.id))

    def _remove_assignment(
        self,
        emp: Any,
        dm: Any,
        sched: Dict,
        estados: Dict[str, EstadoEmpleado],
        coverage_stats: Dict,
    ) -> None:
        """
        Revierte una asignación de sched, estados y coverage_stats.
        Busca por (emp.id, dm.wsid, dm.start, dm.end) en el día correspondiente.
        """
        d = dm.date
        s_min = _t2m(dm.start)
        e_min = _end_min(dm.end)
        emp_id_str = str(emp.id)
        ws_id_str = str(dm.wsid)

        # Quitar de sched (primera ocurrencia)
        day_list = sched.get(d, [])
        for i, (emp2, dm2) in enumerate(day_list):
            if (
                str(emp2.id) == emp_id_str
                and str(getattr(dm2, "wsid", "")) == ws_id_str
                and _t2m(dm2.start) == s_min
                and _end_min(dm2.end) == e_min
            ):
                day_list.pop(i)
                break

        # Quitar de estados
        estados[emp_id_str].desregistrar(d, ws_id_str, s_min, e_min)

        # Actualizar coverage_stats
        dm_id = dm.id
        if dm_id in coverage_stats:
            cs = coverage_stats[dm_id]
            cs["covered"] = max(0, cs.get("covered", 0) - 1)
            cs["met"] = max(0, cs.get("met", 0) - 1)
            cs["unmet"] = cs.get("unmet", 0) + 1
            emp_list = cs.get("employees", [])
            if emp_id_str in emp_list:
                emp_list.remove(emp_id_str)

    def _reconstruct_estados(self, sched: Dict[date, List[Tuple]]) -> Dict[str, EstadoEmpleado]:
        """Reconstruye EstadoEmpleado desde el horario generado."""
        estados: Dict[str, EstadoEmpleado] = {str(e.id): EstadoEmpleado(emp_id=str(e.id)) for e in self.emps}
        for d, assigns in sched.items():
            for emp, dm in assigns:
                ws_id = getattr(dm, "wsid", None)
                if ws_id is None:
                    continue
                if str(ws_id).startswith("HYB:"):
                    continue
                s_min = _t2m(dm.start)
                e_min = _end_min(dm.end)
                emp_key = str(emp.id)
                if emp_key in estados:
                    estados[emp_key].registrar(d, str(ws_id), s_min, e_min)
        return estados

    # ─────────────────────────────────────── BÚSQUEDAS ──────────────────────

    def _find_emp(self, emp_id: str) -> Optional[Any]:
        for e in self.emps:
            if str(e.id) == emp_id:
                return e
        return None

    def _find_demand_for_assignment(self, d: date, ws_id: str, s_min: int, e_min: int) -> Optional[Any]:
        """
        Busca la demanda original que corresponde a una asignación en estados.
        Usa la tabla de búsqueda pre-computada _demands_by_slot.
        """
        key = (d, ws_id, s_min, e_min)
        candidates = self._demands_by_slot.get(key, [])
        return candidates[0] if candidates else None

    def _find_replacement(
        self,
        emp_to_free: Any,
        dm: Any,
        d: date,
        sched: Dict,
        estados: Dict[str, EstadoEmpleado],
    ) -> Optional[Any]:
        """
        Busca un empleado alternativo que pueda tomar la demanda dm en el día d,
        excluyendo al empleado que queremos liberar.
        """
        for alt in self.emps:
            if str(alt.id) == str(emp_to_free.id):
                continue
            ok, _ = self.validador.puede_asignar(alt, dm, d, estados[str(alt.id)], self.overrides)
            if ok:
                return alt
        return None

    def validate_schedule_integrity(self, sched: Dict, coverage_stats: Dict) -> Tuple[bool, List[str]]:
        """
        Valida la integridad básica del horario: sin solapamientos y
        cobertura coherente con sched.

        Retorna (is_valid, lista_de_errores).
        """
        errors: List[str] = []
        estados = self._reconstruct_estados(sched)

        for emp_id, est in estados.items():
            for d, ivs in est.intervalos_por_dia.items():
                for i, (s1, e1) in enumerate(ivs):
                    for s2, e2 in ivs[i + 1 :]:
                        if not (e1 <= s2 or e2 <= s1):
                            errors.append(f"Solapamiento detectado: emp={emp_id} día={d} " f"({s1}-{e1}) ∩ ({s2}-{e2})")

        # Verificar coherencia de coverage_stats
        covered_in_sched: Dict[Any, int] = defaultdict(int)
        for d, assigns in sched.items():
            for emp, dm in assigns:
                if getattr(dm, "wsid", None) is not None:
                    covered_in_sched[dm.id] += 1

        for dm_id, cs in coverage_stats.items():
            expected = covered_in_sched.get(dm_id, 0)
            actual = cs.get("covered", 0)
            if abs(expected - actual) > 1:  # Tolerancia de 1 por híbridos
                errors.append(f"Cobertura inconsistente: demand={dm_id} " f"en_sched={expected} en_stats={actual}")

        return len(errors) == 0, errors
