# services/sugerencias_mejora.py
"""
HU 1.3 - Sistema de Sugerencias de Mejora
==========================================

Esta historia de usuario fue desarrollada pero aún no está desplegada en ambiente QA,
puesto que podría afectar el ambiente actual de la base de datos y bot.

Descripción:
    Analiza los gaps detectados (HU 1.1) y los scores de calidad (HU 1.2) para generar
    sugerencias accionables que mejoren la programación de turnos.

Funcionalidades:
    1. Analiza patrones de gaps recurrentes
    2. Identifica empleados subutilizados o sobrecargados
    3. Sugiere ajustes de ventanas de disponibilidad
    4. Propone contrataciones o capacitaciones necesarias
    5. Detecta reglas que generan conflictos frecuentes

Integración:
    - Se ejecuta después de HU 1.1 y HU 1.2 en el flujo de save()
    - Persiste sugerencias en Management.ScheduleSuggestions
    - Puede consultarse via API /api/agenda/suggestions
"""

from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime, date, time, timedelta
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple
from collections import defaultdict
import json
from uuid import uuid4


# ═══════════════════════════════════════════════════════════════════════════════
# ENUMS Y CONSTANTES
# ═══════════════════════════════════════════════════════════════════════════════

class TipoSugerencia(str, Enum):
    CONTRATAR_PERSONAL = "CONTRATAR_PERSONAL"
    CAPACITAR_EMPLEADO = "CAPACITAR_EMPLEADO"
    AJUSTAR_VENTANA = "AJUSTAR_VENTANA"
    REDISTRIBUIR_CARGA = "REDISTRIBUIR_CARGA"
    RELAJAR_REGLA = "RELAJAR_REGLA"
    AJUSTAR_DEMANDA = "AJUSTAR_DEMANDA"
    SWAP_TURNO = "SWAP_TURNO"
    EXTENDER_HORARIO = "EXTENDER_HORARIO"


class PrioridadSugerencia(str, Enum):
    CRITICA = "CRITICA"      # Afecta cobertura crítica
    ALTA = "ALTA"            # Mejora significativa
    MEDIA = "MEDIA"          # Optimización
    BAJA = "BAJA"            # Nice to have


class ImpactoSugerencia(str, Enum):
    COBERTURA = "COBERTURA"
    EQUIDAD = "EQUIDAD"
    CUMPLIMIENTO = "CUMPLIMIENTO"
    COSTO = "COSTO"


# Umbrales configurables
THRESHOLDS = {
    "gap_recurrence_min": 3,           # Mínimo de ocurrencias para considerarlo recurrente
    "overload_ratio": 1.3,             # Ratio sobre promedio para considerar sobrecarga
    "underload_ratio": 0.7,            # Ratio bajo promedio para considerar subutilización
    "low_coverage_pct": 70.0,          # % de cobertura considerado bajo
    "critical_coverage_pct": 50.0,     # % de cobertura crítico
    "skill_gap_threshold": 2,          # Mínimo gaps por skill para sugerir capacitación
}


# ═══════════════════════════════════════════════════════════════════════════════
# MODELOS DE DATOS
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Sugerencia:
    tipo: TipoSugerencia
    prioridad: PrioridadSugerencia
    titulo: str
    descripcion: str
    impacto_esperado: List[ImpactoSugerencia]
    mejora_estimada: float  # Porcentaje de mejora estimada
    detalles: Dict[str, Any] = field(default_factory=dict)
    empleados_involucrados: List[str] = field(default_factory=list)
    workstations_afectadas: List[str] = field(default_factory=list)
    dias_afectados: List[str] = field(default_factory=list)
    acciones_concretas: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "tipo": self.tipo.value,
            "prioridad": self.prioridad.value,
            "titulo": self.titulo,
            "descripcion": self.descripcion,
            "impacto_esperado": [i.value for i in self.impacto_esperado],
            "mejora_estimada": round(self.mejora_estimada, 2),
            "detalles": self.detalles,
            "empleados_involucrados": self.empleados_involucrados,
            "workstations_afectadas": self.workstations_afectadas,
            "dias_afectados": self.dias_afectados,
            "acciones_concretas": self.acciones_concretas,
        }


@dataclass
class AnalisisGaps:
    """Análisis agregado de gaps para una semana."""
    total_gaps: int = 0
    gaps_por_workstation: Dict[str, int] = field(default_factory=dict)
    gaps_por_dia: Dict[str, int] = field(default_factory=dict)
    gaps_por_hora: Dict[int, int] = field(default_factory=dict)
    gaps_por_categoria: Dict[str, int] = field(default_factory=dict)
    gaps_por_razon: Dict[str, int] = field(default_factory=dict)
    minutos_no_cubiertos: float = 0.0
    cupos_faltantes_total: float = 0.0


@dataclass
class AnalisisEmpleados:
    """Análisis de carga de trabajo por empleado."""
    minutos_por_empleado: Dict[str, int] = field(default_factory=dict)
    dias_por_empleado: Dict[str, int] = field(default_factory=dict)
    promedio_minutos: float = 0.0
    promedio_dias: float = 0.0
    sobrecargados: List[str] = field(default_factory=list)
    subutilizados: List[str] = field(default_factory=list)
    sin_asignacion: List[str] = field(default_factory=list)


# ═══════════════════════════════════════════════════════════════════════════════
# SERVICIO PRINCIPAL
# ═══════════════════════════════════════════════════════════════════════════════

class SugerenciasMejoraService:
    """
    Servicio que genera sugerencias de mejora basándose en:
    - Gaps detectados (HU 1.1)
    - Scores de calidad (HU 1.2)
    - Histórico de programaciones
    """

    def __init__(
        self,
        cursor,
        table_name: str = '"Management"."ScheduleSuggestions"',
        thresholds: Optional[Dict[str, Any]] = None,
        debug: bool = True,
    ):
        self.cur = cursor
        self.table_name = table_name
        self.thresholds = thresholds or THRESHOLDS
        self.debug = debug

    def _log(self, msg: str) -> None:
        if self.debug:
            print(f"[HU1.3] {msg}")

    # ─────────────────────────────────────────────────────────────────────────
    # ANÁLISIS DE GAPS
    # ─────────────────────────────────────────────────────────────────────────

    def _analizar_gaps(self, gaps: List[Dict[str, Any]]) -> AnalisisGaps:
        """Analiza y agrega información de los gaps."""
        analisis = AnalisisGaps()
        analisis.total_gaps = len(gaps)

        for gap in gaps:
            # Por workstation
            ws_nombre = gap.get("workstation", {}).get("nombre", "DESCONOCIDO")
            analisis.gaps_por_workstation[ws_nombre] = \
                analisis.gaps_por_workstation.get(ws_nombre, 0) + 1

            # Por día
            slot = gap.get("slot", {})
            inicio_str = slot.get("inicio", "")
            if inicio_str:
                try:
                    dt = datetime.fromisoformat(inicio_str)
                    dia_str = dt.strftime("%A")  # Nombre del día
                    fecha_str = dt.date().isoformat()
                    analisis.gaps_por_dia[fecha_str] = \
                        analisis.gaps_por_dia.get(fecha_str, 0) + 1

                    # Por hora
                    hora = dt.hour
                    analisis.gaps_por_hora[hora] = \
                        analisis.gaps_por_hora.get(hora, 0) + 1
                except ValueError:
                    pass

            # Por categoría
            categoria = gap.get("categoria", "DESCONOCIDA")
            analisis.gaps_por_categoria[categoria] = \
                analisis.gaps_por_categoria.get(categoria, 0) + 1

            # Por razón
            razones = gap.get("razones", {})
            for razon, count in razones.items():
                analisis.gaps_por_razon[razon] = \
                    analisis.gaps_por_razon.get(razon, 0) + int(count)

            # Cupos faltantes
            cobertura = gap.get("cobertura", {})
            analisis.cupos_faltantes_total += float(cobertura.get("faltante", 0))

        return analisis

    # ─────────────────────────────────────────────────────────────────────────
    # ANÁLISIS DE EMPLEADOS
    # ─────────────────────────────────────────────────────────────────────────

    def _analizar_empleados(
        self,
        sched: Dict[date, List[Tuple[Any, Any]]],
        emps: List[Any],
    ) -> AnalisisEmpleados:
        """Analiza distribución de carga entre empleados."""
        analisis = AnalisisEmpleados()

        # Calcular minutos y días por empleado
        dias_trabajados = defaultdict(set)

        for d, asignaciones in sched.items():
            for emp, dm in asignaciones:
                if dm is None or getattr(dm, "wsid", None) is None:
                    continue

                emp_id = str(getattr(emp, "id", emp))
                emp_name = getattr(emp, "name", emp_id)

                # Calcular duración
                st = getattr(dm, "start", time(0, 0))
                en = getattr(dm, "end", time(0, 0))
                st_min = st.hour * 60 + st.minute
                en_min = en.hour * 60 + en.minute
                if en_min <= st_min:
                    en_min += 24 * 60

                minutos = en_min - st_min
                analisis.minutos_por_empleado[emp_name] = \
                    analisis.minutos_por_empleado.get(emp_name, 0) + minutos

                dias_trabajados[emp_name].add(d)

        # Días por empleado
        for emp_name, dias in dias_trabajados.items():
            analisis.dias_por_empleado[emp_name] = len(dias)

        # Promedios
        if analisis.minutos_por_empleado:
            analisis.promedio_minutos = sum(analisis.minutos_por_empleado.values()) / \
                                        len(analisis.minutos_por_empleado)
            analisis.promedio_dias = sum(analisis.dias_por_empleado.values()) / \
                                     len(analisis.dias_por_empleado)

        # Identificar sobrecargados y subutilizados
        overload_threshold = analisis.promedio_minutos * self.thresholds["overload_ratio"]
        underload_threshold = analisis.promedio_minutos * self.thresholds["underload_ratio"]

        for emp_name, minutos in analisis.minutos_por_empleado.items():
            if minutos > overload_threshold:
                analisis.sobrecargados.append(emp_name)
            elif minutos < underload_threshold and minutos > 0:
                analisis.subutilizados.append(emp_name)

        # Empleados sin asignación
        emp_names_asignados = set(analisis.minutos_por_empleado.keys())
        for emp in emps:
            emp_name = getattr(emp, "name", str(getattr(emp, "id", "")))
            if emp_name and emp_name not in emp_names_asignados:
                # Verificar que no esté ausente toda la semana
                absent_days = getattr(emp, "absent", set())
                if len(absent_days) < 7:
                    analisis.sin_asignacion.append(emp_name)

        return analisis

    # ─────────────────────────────────────────────────────────────────────────
    # GENERACIÓN DE SUGERENCIAS
    # ─────────────────────────────────────────────────────────────────────────

    def _generar_sugerencias_gaps(
        self,
        gaps: List[Dict[str, Any]],
        analisis_gaps: AnalisisGaps,
    ) -> List[Sugerencia]:
        """Genera sugerencias basadas en análisis de gaps."""
        sugerencias = []

        # 1. Gaps recurrentes por workstation -> Contratar/Capacitar
        for ws_nombre, count in analisis_gaps.gaps_por_workstation.items():
            if count >= self.thresholds["gap_recurrence_min"]:
                sugerencias.append(Sugerencia(
                    tipo=TipoSugerencia.CONTRATAR_PERSONAL,
                    prioridad=PrioridadSugerencia.ALTA if count >= 5 else PrioridadSugerencia.MEDIA,
                    titulo=f"Reforzar cobertura en {ws_nombre}",
                    descripcion=f"Se detectaron {count} gaps en {ws_nombre} esta semana. "
                               f"Considerar contratar personal adicional o capacitar empleados existentes.",
                    impacto_esperado=[ImpactoSugerencia.COBERTURA],
                    mejora_estimada=min(15.0 * (count / 5), 30.0),
                    workstations_afectadas=[ws_nombre],
                    acciones_concretas=[
                        f"Publicar vacante para {ws_nombre} (tiempo parcial o completo)",
                        f"Identificar empleados que puedan capacitarse en {ws_nombre}",
                        f"Revisar si la demanda de {ws_nombre} está sobreestimada",
                    ],
                    detalles={"gaps_detectados": count}
                ))

        # 2. Gaps por SKILL_FALTANTE -> Capacitación específica
        skill_gaps = analisis_gaps.gaps_por_razon.get("SKILL_FALTANTE", 0)
        if skill_gaps >= self.thresholds["skill_gap_threshold"]:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.CAPACITAR_EMPLEADO,
                prioridad=PrioridadSugerencia.ALTA,
                titulo="Programa de capacitación cruzada necesario",
                descripcion=f"Se detectaron {skill_gaps} bloqueos por falta de skill. "
                           f"Implementar programa de capacitación cruzada.",
                impacto_esperado=[ImpactoSugerencia.COBERTURA, ImpactoSugerencia.EQUIDAD],
                mejora_estimada=min(10.0 * (skill_gaps / 3), 25.0),
                acciones_concretas=[
                    "Identificar los puestos con mayor déficit de personal capacitado",
                    "Seleccionar empleados con potencial para capacitación cruzada",
                    "Programar sesiones de entrenamiento en horarios de baja demanda",
                ],
                detalles={"bloqueos_por_skill": skill_gaps}
            ))

        # 3. Gaps por FUERA_DE_VENTANA -> Ajustar disponibilidad
        ventana_gaps = analisis_gaps.gaps_por_razon.get("FUERA_DE_VENTANA", 0)
        if ventana_gaps >= self.thresholds["gap_recurrence_min"]:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.AJUSTAR_VENTANA,
                prioridad=PrioridadSugerencia.MEDIA,
                titulo="Revisar ventanas de disponibilidad",
                descripcion=f"Se detectaron {ventana_gaps} gaps porque los empleados "
                           f"no están disponibles en esos horarios.",
                impacto_esperado=[ImpactoSugerencia.COBERTURA],
                mejora_estimada=min(8.0 * (ventana_gaps / 3), 20.0),
                acciones_concretas=[
                    "Revisar UserShifts y ventanas de disponibilidad configuradas",
                    "Negociar con empleados extensión de horarios disponibles",
                    "Contratar personal con disponibilidad en horarios descubiertos",
                ],
                detalles={"bloqueos_por_ventana": ventana_gaps}
            ))

        # 4. Gaps concentrados en horario específico
        max_hora = max(analisis_gaps.gaps_por_hora.items(), key=lambda x: x[1], default=(None, 0))
        if max_hora[0] is not None and max_hora[1] >= 3:
            hora_str = f"{max_hora[0]:02d}:00"
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.AJUSTAR_DEMANDA,
                prioridad=PrioridadSugerencia.MEDIA,
                titulo=f"Revisar demanda en horario {hora_str}",
                descripcion=f"Se concentran {max_hora[1]} gaps alrededor de las {hora_str}. "
                           f"Revisar si la demanda es correcta o ajustar turnos.",
                impacto_esperado=[ImpactoSugerencia.COBERTURA],
                mejora_estimada=10.0,
                acciones_concretas=[
                    f"Verificar demanda real a las {hora_str} con datos históricos",
                    "Ajustar hora de inicio/fin de turnos para cubrir este horario",
                    "Considerar turno específico para cubrir pico",
                ],
                detalles={"hora_pico": hora_str, "gaps_en_hora": max_hora[1]}
            ))

        return sugerencias

    def _generar_sugerencias_empleados(
        self,
        analisis_emp: AnalisisEmpleados,
    ) -> List[Sugerencia]:
        """Genera sugerencias basadas en análisis de carga de empleados."""
        sugerencias = []

        # 1. Empleados sobrecargados
        if analisis_emp.sobrecargados:
            horas_promedio = round(analisis_emp.promedio_minutos / 60, 1)
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.REDISTRIBUIR_CARGA,
                prioridad=PrioridadSugerencia.ALTA,
                titulo="Redistribuir carga de trabajo",
                descripcion=f"Hay {len(analisis_emp.sobrecargados)} empleados con carga "
                           f"superior al 130% del promedio ({horas_promedio}h). "
                           f"Redistribuir para evitar burnout.",
                impacto_esperado=[ImpactoSugerencia.EQUIDAD, ImpactoSugerencia.CUMPLIMIENTO],
                mejora_estimada=15.0,
                empleados_involucrados=analisis_emp.sobrecargados[:5],
                acciones_concretas=[
                    "Revisar asignaciones de empleados sobrecargados",
                    "Reasignar turnos a empleados subutilizados",
                    "Verificar cumplimiento de horas máximas legales",
                ],
                detalles={
                    "sobrecargados": analisis_emp.sobrecargados,
                    "promedio_minutos": round(analisis_emp.promedio_minutos, 0),
                }
            ))

        # 2. Empleados subutilizados
        if analisis_emp.subutilizados and len(analisis_emp.subutilizados) >= 2:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.REDISTRIBUIR_CARGA,
                prioridad=PrioridadSugerencia.MEDIA,
                titulo="Aprovechar capacidad disponible",
                descripcion=f"Hay {len(analisis_emp.subutilizados)} empleados con carga "
                           f"inferior al 70% del promedio. Considerar asignarles más turnos.",
                impacto_esperado=[ImpactoSugerencia.EQUIDAD, ImpactoSugerencia.COBERTURA],
                mejora_estimada=10.0,
                empleados_involucrados=analisis_emp.subutilizados[:5],
                acciones_concretas=[
                    "Verificar disponibilidad real de estos empleados",
                    "Asignar turnos adicionales donde hay gaps",
                    "Revisar si hay restricciones que limitan su asignación",
                ],
                detalles={"subutilizados": analisis_emp.subutilizados}
            ))

        # 3. Empleados sin asignación
        if analisis_emp.sin_asignacion:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.REDISTRIBUIR_CARGA,
                prioridad=PrioridadSugerencia.CRITICA if len(analisis_emp.sin_asignacion) >= 3 else PrioridadSugerencia.ALTA,
                titulo="Empleados sin asignación",
                descripcion=f"Hay {len(analisis_emp.sin_asignacion)} empleados que no "
                           f"recibieron ningún turno esta semana.",
                impacto_esperado=[ImpactoSugerencia.EQUIDAD, ImpactoSugerencia.COSTO],
                mejora_estimada=20.0,
                empleados_involucrados=analisis_emp.sin_asignacion[:5],
                acciones_concretas=[
                    "Verificar si estos empleados están activos y disponibles",
                    "Revisar sus roles y capacitaciones",
                    "Asignar turnos en gaps detectados",
                ],
                detalles={"sin_asignacion": analisis_emp.sin_asignacion}
            ))

        return sugerencias

    def _generar_sugerencias_scores(
        self,
        quality_result: Dict[str, Any],
    ) -> List[Sugerencia]:
        """Genera sugerencias basadas en scores de calidad."""
        sugerencias = []

        score_total = quality_result.get("score", 100)
        coverage_score = quality_result.get("breakdown", {}).get("coverage", 100)
        fairness_score = quality_result.get("breakdown", {}).get("fairness", 100)
        rules_score = quality_result.get("breakdown", {}).get("rules", 100)

        # 1. Cobertura baja
        if coverage_score < self.thresholds["critical_coverage_pct"]:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.CONTRATAR_PERSONAL,
                prioridad=PrioridadSugerencia.CRITICA,
                titulo="¡Cobertura crítica!",
                descripcion=f"La cobertura está en {coverage_score:.1f}%, muy por debajo "
                           f"del mínimo aceptable. Se requiere acción inmediata.",
                impacto_esperado=[ImpactoSugerencia.COBERTURA],
                mejora_estimada=30.0,
                acciones_concretas=[
                    "Contratar personal temporal/refuerzo de emergencia",
                    "Activar lista de empleados de guardia",
                    "Revisar demanda y ajustar expectativas",
                ],
                detalles={"coverage_score": coverage_score}
            ))
        elif coverage_score < self.thresholds["low_coverage_pct"]:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.CONTRATAR_PERSONAL,
                prioridad=PrioridadSugerencia.ALTA,
                titulo="Cobertura por debajo del objetivo",
                descripcion=f"La cobertura está en {coverage_score:.1f}%. "
                           f"Se recomienda reforzar la plantilla.",
                impacto_esperado=[ImpactoSugerencia.COBERTURA],
                mejora_estimada=15.0,
                acciones_concretas=[
                    "Analizar gaps y determinar puestos prioritarios",
                    "Publicar vacantes o activar bolsa de trabajo",
                ],
                detalles={"coverage_score": coverage_score}
            ))

        # 2. Equidad baja
        if fairness_score < 60:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.REDISTRIBUIR_CARGA,
                prioridad=PrioridadSugerencia.MEDIA,
                titulo="Distribución de horas desigual",
                descripcion=f"El score de equidad es {fairness_score:.1f}%. "
                           f"La carga de trabajo no está bien distribuida.",
                impacto_esperado=[ImpactoSugerencia.EQUIDAD],
                mejora_estimada=10.0,
                acciones_concretas=[
                    "Revisar asignación de empleados con más/menos horas",
                    "Balancear turnos entre empleados similares",
                    "Verificar que no haya favoritismos en la asignación",
                ],
                detalles={"fairness_score": fairness_score}
            ))

        # 3. Violaciones de reglas
        if rules_score < 80:
            sugerencias.append(Sugerencia(
                tipo=TipoSugerencia.RELAJAR_REGLA,
                prioridad=PrioridadSugerencia.MEDIA,
                titulo="Revisar configuración de reglas",
                descripcion=f"El score de cumplimiento de reglas es {rules_score:.1f}%. "
                           f"Algunas restricciones pueden estar muy ajustadas.",
                impacto_esperado=[ImpactoSugerencia.CUMPLIMIENTO],
                mejora_estimada=8.0,
                acciones_concretas=[
                    "Revisar reglas que generan más conflictos",
                    "Evaluar si algunas restricciones pueden relajarse",
                    "Verificar configuración de descansos y máximos",
                ],
                detalles={"rules_score": rules_score}
            ))

        return sugerencias

    # ─────────────────────────────────────────────────────────────────────────
    # PERSISTENCIA
    # ─────────────────────────────────────────────────────────────────────────

    def guardar_sugerencias(
        self,
        sugerencias: List[Sugerencia],
        token: str,
        week_start: date,
        week_end: date,
    ) -> int:
        """Persiste las sugerencias en la base de datos."""
        if not sugerencias:
            self._log("No hay sugerencias para guardar")
            return 0

        sql = f"""
            INSERT INTO {self.table_name}
              ("Id", "Token", "WeekStart", "WeekEnd", "Tipo", "Prioridad",
               "Titulo", "Descripcion", "ImpactoEsperado", "MejoraEstimada",
               "Detalles", "EmpleadosInvolucrados", "WorkstationsAfectadas",
               "DiasAfectados", "AccionesConcretas", "CreatedAt")
            VALUES
              (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """

        inserted = 0
        now_dt = datetime.utcnow()

        for sug in sugerencias:
            try:
                self.cur.execute(sql, (
                    str(uuid4()),
                    token,
                    week_start,
                    week_end,
                    sug.tipo.value,
                    sug.prioridad.value,
                    sug.titulo,
                    sug.descripcion,
                    json.dumps([i.value for i in sug.impacto_esperado]),
                    sug.mejora_estimada,
                    json.dumps(sug.detalles, ensure_ascii=False),
                    json.dumps(sug.empleados_involucrados),
                    json.dumps(sug.workstations_afectadas),
                    json.dumps(sug.dias_afectados),
                    json.dumps(sug.acciones_concretas, ensure_ascii=False),
                    now_dt,
                ))
                inserted += 1
            except Exception as e:
                self._log(f"Error insertando sugerencia: {e}")

        self._log(f"Insertadas {inserted} sugerencias en {self.table_name}")
        return inserted

    # ─────────────────────────────────────────────────────────────────────────
    # ORQUESTACIÓN
    # ─────────────────────────────────────────────────────────────────────────

    def generar_y_guardar(
        self,
        gaps: List[Dict[str, Any]],
        sched: Dict[date, List[Tuple[Any, Any]]],
        emps: List[Any],
        quality_result: Dict[str, Any],
        token: str,
        week_start: date,
        week_end: date,
    ) -> List[Dict[str, Any]]:
        """
        Genera y guarda todas las sugerencias de mejora.

        Args:
            gaps: Lista de explicaciones de gaps (de HU 1.1)
            sched: Schedule generado (dict date -> [(emp, dm)])
            emps: Lista de empleados
            quality_result: Resultado del cálculo de calidad (de HU 1.2)
            token: Token del schedule
            week_start: Fecha inicio de semana
            week_end: Fecha fin de semana

        Returns:
            Lista de sugerencias como diccionarios
        """
        self._log(f"==== START generar_y_guardar token={token} ====")

        todas_sugerencias: List[Sugerencia] = []

        # 1. Analizar y generar sugerencias de gaps
        analisis_gaps = self._analizar_gaps(gaps)
        self._log(f"Gaps analizados: {analisis_gaps.total_gaps}")
        sugerencias_gaps = self._generar_sugerencias_gaps(gaps, analisis_gaps)
        todas_sugerencias.extend(sugerencias_gaps)
        self._log(f"Sugerencias de gaps: {len(sugerencias_gaps)}")

        # 2. Analizar y generar sugerencias de empleados
        analisis_emp = self._analizar_empleados(sched, emps)
        self._log(f"Empleados analizados: {len(analisis_emp.minutos_por_empleado)}")
        sugerencias_emp = self._generar_sugerencias_empleados(analisis_emp)
        todas_sugerencias.extend(sugerencias_emp)
        self._log(f"Sugerencias de empleados: {len(sugerencias_emp)}")

        # 3. Generar sugerencias de scores
        sugerencias_scores = self._generar_sugerencias_scores(quality_result)
        todas_sugerencias.extend(sugerencias_scores)
        self._log(f"Sugerencias de scores: {len(sugerencias_scores)}")

        # 4. Ordenar por prioridad
        prioridad_orden = {
            PrioridadSugerencia.CRITICA: 0,
            PrioridadSugerencia.ALTA: 1,
            PrioridadSugerencia.MEDIA: 2,
            PrioridadSugerencia.BAJA: 3,
        }
        todas_sugerencias.sort(key=lambda s: prioridad_orden.get(s.prioridad, 4))

        # 5. Guardar
        inserted = self.guardar_sugerencias(todas_sugerencias, token, week_start, week_end)
        self._log(f"==== END generar_y_guardar inserted={inserted} ====")

        return [s.to_dict() for s in todas_sugerencias]


