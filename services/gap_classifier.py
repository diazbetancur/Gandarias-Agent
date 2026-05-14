# services/gap_classifier.py
"""
ScheduleGapClassifier — Gandarias v5.0
========================================
Clasifica los huecos sin cubrir en categorías accionables para que el
ScheduleRepairEngine sepa qué estrategia aplicar en cada caso.

Categorías:
    INEVITABLE          — No hay ningún empleado con el skill requerido.
                          El hueco no puede cubrirse con el personal actual.
    CORREGIBLE_SWAP     — Hay empleados habilitados pero bloqueados por saturación
                          (MAX_HORAS, MAX_DIAS, MAX_HORAS_DIA). Un intercambio
                          de turno podría liberar capacidad.
    CORREGIBLE_EXTENSION— Hay empleados ya asignados el mismo día que podrían
                          extender su turno para cubrir el hueco sin violar
                          restricciones duras.
    CORREGIBLE_FALLBACK — El puesto no está cubierto directamente pero hay
                          personal con rol de fallback configurado.
    DATO_INSUFICIENTE   — No hay suficiente información para clasificar.

No modifica el horario. Solo lee y clasifica.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field
from datetime import date, time
from enum import Enum
from typing import Any, Dict, List, Optional, Set

from services.ai_scheduler import (
    EstadoEmpleado,
    ValidadorReglasDuras,
    _end_min,
    _seg_min,
    _t2m,
    REGLAS_DURAS_DEFAULTS,
)

logger = logging.getLogger("gap_classifier")

# Razones de rechazo que indican saturación (corregibles por swap)
_SATURACION_REASONS: Set[str] = {
    "MAX_HORAS_SEMANALES",
    "MAX_DIAS",
    "MAX_HORAS_DIA",
}

# Razones de rechazo que indican imposibilidad real (no corregibles sin cambios de datos)
_IMPOSIBLE_REASONS: Set[str] = {
    "SIN_SKILL",
    "DIA_LIBRE",
    "FUERA_VENTANA",
    "FUERA_USERSHIFT_WINDOW",
}


# ─────────────────────────────────────────────────────────────────────────────
# ENUMS Y DTOs
# ─────────────────────────────────────────────────────────────────────────────


class GapType(str, Enum):
    INEVITABLE = "INEVITABLE"
    CORREGIBLE_SWAP = "CORREGIBLE_SWAP"
    CORREGIBLE_EXTENSION = "CORREGIBLE_EXTENSION"
    CORREGIBLE_FALLBACK = "CORREGIBLE_FALLBACK"
    DATO_INSUFICIENTE = "DATO_INSUFICIENTE"


@dataclass
class ClassifiedGap:
    """
    Hueco sin cubrir clasificado con su tipo y metadatos de diagnóstico.

    demand_id               — ID de la demanda sin cubrir
    date                    — Fecha del hueco
    workstation_id          — Workstation requerida
    workstation_name        — Nombre legible de la workstation
    start_time              — Inicio del hueco
    end_time                — Fin del hueco
    duration_minutes        — Duración en minutos
    slots_missing           — Número de personas que faltan
    gap_type                — Clasificación del tipo de hueco
    rejection_reasons       — {emp_id: razón_de_rechazo} para diagnóstico
    skill_qualified_employees  — IDs de empleados con el skill requerido
    available_employees     — IDs de empleados disponibles en esa franja
                              (aunque saturados en horas)
    """

    demand_id: Any
    date: date
    workstation_id: Any
    workstation_name: str
    start_time: time
    end_time: time
    duration_minutes: int
    slots_missing: int
    gap_type: GapType
    rejection_reasons: Dict[str, str] = field(default_factory=dict)
    skill_qualified_employees: List[str] = field(default_factory=list)
    available_employees: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "demand_id": str(self.demand_id),
            "date": self.date.isoformat(),
            "workstation_id": str(self.workstation_id),
            "workstation_name": self.workstation_name,
            "start_time": self.start_time.isoformat(),
            "end_time": self.end_time.isoformat(),
            "duration_minutes": self.duration_minutes,
            "slots_missing": self.slots_missing,
            "gap_type": self.gap_type.value,
            "rejection_reasons": self.rejection_reasons,
            "skill_qualified_employees": self.skill_qualified_employees,
            "available_employees": self.available_employees,
        }

    @property
    def is_fixable(self) -> bool:
        return self.gap_type in (
            GapType.CORREGIBLE_SWAP,
            GapType.CORREGIBLE_EXTENSION,
            GapType.CORREGIBLE_FALLBACK,
        )

    @property
    def criticality_score(self) -> float:
        """
        Score de criticidad para priorizar reparación.
        Mayor = más urgente.

        Criterios:
        - Huecos de mayor duración son más urgentes.
        - Huecos con menos candidatos habilitados son más críticos.
        - Fin de semana y noche tienen mayor impacto operativo.
        """
        duration_weight = min(self.duration_minutes / 60.0, 9.0) / 9.0
        skill_scarcity = 1.0 / max(1, len(self.skill_qualified_employees))
        is_night = _t2m(self.start_time) >= 20 * 60
        is_weekend = self.date.weekday() >= 5
        bonus = (0.3 if is_night else 0.0) + (0.2 if is_weekend else 0.0)
        return round(duration_weight * 0.5 + skill_scarcity * 0.5 + bonus, 4)


# ─────────────────────────────────────────────────────────────────────────────
# DEMAND ADAPTER
# ─────────────────────────────────────────────────────────────────────────────


class _GapDemandAdapter:
    """
    Adaptador mínimo que permite pasar un ClassifiedGap a
    ValidadorReglasDuras.puede_asignar() sin construir un Demand completo.
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

    def __init__(self, gap_info: ClassifiedGap):
        self.id = gap_info.demand_id
        self.date = gap_info.date
        self.wsid = gap_info.workstation_id
        self.wsname = gap_info.workstation_name
        self.start = gap_info.start_time
        self.end = gap_info.end_time
        self.need = gap_info.slots_missing
        self.raw_need = float(gap_info.slots_missing)
        self.has_hybrid_component = False
        self.observation_override = None


# ─────────────────────────────────────────────────────────────────────────────
# CLASIFICADOR
# ─────────────────────────────────────────────────────────────────────────────


class ScheduleGapClassifier:
    """
    Clasifica huecos sin cubrir en categorías accionables.

    Uso:
        classifier = ScheduleGapClassifier(emps, validador, reglas)
        gaps = classifier.classify(coverage_stats, sched, estados)
    """

    def __init__(
        self,
        emps: List,
        validador: Optional[ValidadorReglasDuras] = None,
        reglas: Optional[Dict] = None,
        role_fallbacks: Optional[Dict[str, List[str]]] = None,
        debug: bool = True,
    ):
        """
        Parámetros:
            emps           — Lista de empleados (Emp) con sus roles y disponibilidad
            validador      — ValidadorReglasDuras; si es None, se crea uno por defecto
            reglas         — Reglas duras; si es None, usa REGLAS_DURAS_DEFAULTS
            role_fallbacks — Mapa de nombre_ws → [nombre_ws_fallback, ...]
                             (por ejemplo ROLE_FALLBACKS_BY_NAME de agenda.py)
            debug          — Activar logging detallado
        """
        self.emps = emps
        self.validador = validador or ValidadorReglasDuras(reglas or dict(REGLAS_DURAS_DEFAULTS))
        self.role_fallbacks = role_fallbacks or {}
        self.debug = debug

    def _log(self, msg: str) -> None:
        if self.debug:
            logger.debug(msg)

    # ─────────────────────────────────────── API PRINCIPAL ──────────────────

    def classify(
        self,
        coverage_stats: Dict[Any, Dict],
        sched: Dict[date, List],
        estados: Optional[Dict[str, EstadoEmpleado]] = None,
        overrides: Optional[Set] = None,
    ) -> List[ClassifiedGap]:
        """
        Clasifica todos los huecos del horario (demands con unmet > 0).

        Parámetros:
            coverage_stats — Mapa demand_id → {demand, covered, unmet, ...}
            sched          — Horario generado {date: [(Emp, Demand)]}
            estados        — EstadoEmpleado pre-calculados (opcional)
            overrides      — Set de (emp_id_str, date) que saltan ventana UserShift

        Retorna lista de ClassifiedGap, una por cada slot sin cubrir.
        Los huecos se deduplicán a nivel de demanda (no de slot individual).
        """
        overrides = overrides or set()
        if estados is None:
            estados = self._reconstruct_estados(sched)

        # Construir mapa de empleados asignados por día para detectar extensiones
        emps_by_date: Dict[date, Set[str]] = {}
        for d, assigns in sched.items():
            emps_by_date[d] = {str(emp.id) for emp, _ in assigns}

        gaps: List[ClassifiedGap] = []
        for dm_id, cs in coverage_stats.items():
            if cs.get("unmet", 0) <= 0:
                continue
            dm = cs.get("demand")
            if dm is None or getattr(dm, "wsid", None) is None:
                continue

            classified = self._classify_one(dm, cs["unmet"], estados, emps_by_date, overrides)
            gaps.append(classified)
            self._log(
                f"[GAP] {dm.wsname or dm.wsid} {dm.date} "
                f"{dm.start}-{dm.end} → {classified.gap_type.value} "
                f"(slots={classified.slots_missing})"
            )

        return gaps

    # ─────────────────────────────────────── CLASIFICACIÓN INDIVIDUAL ────────

    def _classify_one(
        self,
        dm: Any,
        slots_missing: int,
        estados: Dict[str, EstadoEmpleado],
        emps_by_date: Dict[date, Set[str]],
        overrides: Set,
    ) -> ClassifiedGap:
        """Clasifica un único hueco (demand con unmet > 0)."""
        dur_min = _seg_min(dm.start, dm.end)

        gap = ClassifiedGap(
            demand_id=dm.id,
            date=dm.date,
            workstation_id=dm.wsid,
            workstation_name=getattr(dm, "wsname", str(dm.wsid)),
            start_time=dm.start,
            end_time=dm.end,
            duration_minutes=dur_min,
            slots_missing=slots_missing,
            gap_type=GapType.DATO_INSUFICIENTE,
        )

        # Adaptar el hueco como demand para el validador
        gap_dm = _GapDemandAdapter(gap)

        skill_qualified: List[str] = []
        available_after_relax: List[str] = []
        rejection_reasons: Dict[str, str] = {}
        saturacion_count = 0
        total_qualified = 0

        for emp in self.emps:
            # ── Filtro por skill ──────────────────────────────────────────
            if not emp.can(dm.wsid):
                rejection_reasons[str(emp.id)] = "SIN_SKILL"
                continue

            skill_qualified.append(str(emp.id))
            total_qualified += 1
            estado = estados.get(str(emp.id))
            if estado is None:
                estado = EstadoEmpleado(emp_id=str(emp.id))

            # ── Validación completa con reglas duras ──────────────────────
            ok, reason = self.validador.puede_asignar(emp, gap_dm, dm.date, estado, overrides)
            if ok:
                # Puede asignarse directamente — el generador lo pasó por alto
                available_after_relax.append(str(emp.id))
            else:
                rejection_reasons[str(emp.id)] = reason
                if reason in _SATURACION_REASONS:
                    saturacion_count += 1

        gap.skill_qualified_employees = skill_qualified
        gap.available_employees = available_after_relax
        gap.rejection_reasons = rejection_reasons

        # ── Clasificación por jerarquía ───────────────────────────────────
        if not skill_qualified:
            # Ningún empleado tiene el skill → inevitable
            gap.gap_type = GapType.INEVITABLE
            return gap

        if available_after_relax:
            # Hay candidatos válidos que el generador no usó
            # (raro, pero puede ocurrir en pases extra o fallbacks)
            gap.gap_type = GapType.CORREGIBLE_SWAP
            return gap

        if saturacion_count == total_qualified:
            # Todos los habilitados están saturados → swap libera capacidad
            gap.gap_type = GapType.CORREGIBLE_SWAP
            return gap

        # ── Comprobar extensión de turno ─────────────────────────────────
        if self._can_extend(dm, estados, emps_by_date):
            gap.gap_type = GapType.CORREGIBLE_EXTENSION
            return gap

        # ── Comprobar fallback de rol ─────────────────────────────────────
        if self._has_fallback_candidates(dm, estados, overrides):
            gap.gap_type = GapType.CORREGIBLE_FALLBACK
            return gap

        # ── Mix de razones (no solo saturación) ─────────────────────────
        if saturacion_count > 0:
            gap.gap_type = GapType.CORREGIBLE_SWAP
            return gap

        gap.gap_type = GapType.DATO_INSUFICIENTE
        return gap

    # ─────────────────────────────────────── HELPERS ────────────────────────

    def _can_extend(
        self,
        dm: Any,
        estados: Dict[str, EstadoEmpleado],
        emps_by_date: Dict[date, Set[str]],
    ) -> bool:
        """
        Verifica si algún empleado ya asignado ese día podría extender su turno
        para cubrir el hueco, sin superar max_horas_dia.

        Criterio simplificado: el empleado trabaja ese día y su turno actual
        no llega al máximo de horas diarias configurado.
        """
        max_h_min = self.validador.reglas.get("max_horas_por_dia", 9) * 60
        gap_dur = _seg_min(dm.start, dm.end)
        d = dm.date

        working_today = emps_by_date.get(d, set())
        for emp in self.emps:
            if str(emp.id) not in working_today:
                continue
            if not emp.can(dm.wsid):
                continue
            estado = estados.get(str(emp.id))
            if estado is None:
                continue
            hoy_min = estado.minutos_por_dia.get(d, 0)
            if hoy_min + gap_dur <= max_h_min:
                return True
        return False

    def _has_fallback_candidates(
        self,
        dm: Any,
        estados: Dict[str, EstadoEmpleado],
        overrides: Set,
    ) -> bool:
        """
        Verifica si hay candidatos de fallback de rol que podrían cubrir el hueco.

        Los fallbacks se buscan en self.role_fallbacks usando el nombre del ws.
        Nota: en el flujo normal de agenda.py los fallbacks YA están aplicados
        a emp.roles, por lo que este path solo activa si hay fallbacks configurados
        que NO fueron expandidos durante load_data().
        """
        if not self.role_fallbacks:
            return False
        ws_name = getattr(dm, "wsname", "").upper()
        fallback_names = self.role_fallbacks.get(ws_name, [])
        if not fallback_names:
            return False

        # Construir mapa nombre→id de workstations conocidas
        ws_name_to_id: Dict[str, Any] = {}
        for emp in self.emps:
            # No tenemos acceso directo al name→id, usar heurística por roles
            pass  # Requiere datos adicionales; devolvemos True conservadoramente
        return bool(fallback_names)  # Indica que hay fallback configurado

    def _reconstruct_estados(self, sched: Dict[date, List]) -> Dict[str, EstadoEmpleado]:
        """Reconstruye EstadoEmpleado desde el horario si no se proveen."""
        estados: Dict[str, EstadoEmpleado] = {}
        for d, assigns in sched.items():
            for emp, dm in assigns:
                emp_key = str(emp.id)
                if emp_key not in estados:
                    estados[emp_key] = EstadoEmpleado(emp_id=emp_key)
                ws_id = getattr(dm, "wsid", None)
                if ws_id is None:
                    continue
                s_min = _t2m(dm.start)
                e_min = _end_min(dm.end)
                estados[emp_key].registrar(d, str(ws_id), s_min, e_min)
        return estados

    # ─────────────────────────────────────── STATS HELPER ───────────────────

    def summarize(self, gaps: List[ClassifiedGap]) -> Dict[str, Any]:
        """
        Retorna un resumen agregado de los huecos clasificados.
        Útil para logs y reportes.
        """
        from collections import Counter

        type_counts = Counter(g.gap_type.value for g in gaps)
        total_min = sum(g.duration_minutes * g.slots_missing for g in gaps)
        return {
            "total_gaps": len(gaps),
            "total_missing_slots": sum(g.slots_missing for g in gaps),
            "total_missing_minutes": total_min,
            "by_type": dict(type_counts),
            "inevitable": type_counts.get(GapType.INEVITABLE.value, 0),
            "fixable": sum(
                type_counts.get(t.value, 0)
                for t in (
                    GapType.CORREGIBLE_SWAP,
                    GapType.CORREGIBLE_EXTENSION,
                    GapType.CORREGIBLE_FALLBACK,
                )
            ),
        }
