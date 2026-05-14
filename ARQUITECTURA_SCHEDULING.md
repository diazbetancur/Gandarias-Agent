# Informe de Arquitectura y Optimización — Gandarias Scheduling Engine v5.0

> **Base de análisis:** `ai_scheduler.py`, `agenda.py`, `validador_reglas.py`, `puntaje_calidad_turno.py`, `explicador_huecos.py`, `sugerencias_mejora.py`, `aprendizaje_historico.py`
> **Fecha:** Mayo 2026

---

## 1. Resumen Ejecutivo

### Estado actual del sistema

El motor actual (v5.0) es una **heurística greedy constructiva multi-fase** con aprendizaje histórico, validación de restricciones duras en tiempo real, scoring de candidatos y relajación progresiva de restricciones blandas. Es un sistema bien estructurado y con niveles de sofisticación notables para una heurística construida a medida.

**Cobertura del 90%:** Es una base sólida pero evidencia un problema estructural concreto. El 10% restante no es aleatorio —el sistema ya lo diagnostica con `[DIAG-WS]` y `[DIAG]`— pero **no puede repararlo** porque carece de mecanismos de backtracking o intercambio de asignaciones ya realizadas. El sistema llega al 90% y se detiene, no porque no haya más capacidad algorítmica, sino porque la estrategia greedy queda atrapada en un estado local sin poder reorganizarse.

### Principal riesgo de seguir solo con heurística

El riesgo concreto del sistema actual es la **irrecuperabilidad de decisiones tempranas**. Cuando el algoritmo asigna un empleado en la Fase 1 basándose en su score de balance, esa decisión puede impedir cubrir una demanda posterior que solo ese empleado podía cubrir. El sistema detecta el hueco con el diagnóstico, pero no puede volver atrás.

### Recomendación de tipo de mejora

**En orden de prioridad e impacto:**

1. **Repair Engine** — máximo impacto, coste bajo, no rompe nada existente
2. **Inversión del orden de prioridad** — corrección puntual en la lógica actual (ver sección 2)
3. **Score Engine refinado** — ya existe, necesita dos ajustes
4. **IA explicativa** — ya existe parcialmente (`explicador_huecos.py`, `sugerencias_mejora.py`), necesita despliegue y afinado

**No se recomienda todavía:** solver formal (OR-Tools), algoritmos genéticos ni reemplazo del core.

---

## 2. Diagnóstico Técnico del Modelo Actual

### Tipo de heurística

El motor es una **heurística greedy constructiva multi-fase con relajación progresiva**. Específicamente:

- **Fase constructiva** (`_fase_hibridos` → bucle principal → `_pase_extra` × N): asigna uno a uno, eligiendo el mejor candidato según score.
- **Relajación progresiva** (RELAX-1 a RELAX-4): cuando la cobertura no alcanza el piso, afloja restricciones blandas en cascada.
- **Aprendizaje estadístico** (`ExtractorPatrones`): no IA en sentido estricto, sino extracción de patrones históricos (afinidad emp-ws, horarios típicos, carga histórica).

### Lo que decide bien

| Decisión                          | Por qué funciona                                                                                          |
| --------------------------------- | --------------------------------------------------------------------------------------------------------- |
| Orden de demandas por criticidad  | Procesa primero las demandas con menos candidatos disponibles y las nocturnas/fin de semana               |
| Scorer multi-criterio con pesos   | Balance semanal (0.22) + balance diario (0.22) + déficit (0.20) = 64% orientado a distribución equitativa |
| Relajación progresiva documentada | Las 4 fases de relajación siguen las reglas del PDF de negocio, no improvisan                             |
| Validación dura precisa           | `puede_asignar` valida 10 restricciones en cadena antes de cualquier asignación                           |
| Diagnóstico de rechazos           | `[DIAG-WS]` identifica qué puestos quedan sin cubrir y cuántos empleados los pueden cubrir                |
| Desregistro limpio                | `desregistrar()` permite revertir asignaciones manteniendo el estado consistente                          |

### Lo que puede estar causando huecos

**Problema 1 — Conflicto entre balance y cobertura en el scorer:**

El scorer pondera balance/equidad con un 64% del peso total (semanal + diario + déficit). Esto es correcto para distribuir carga, pero crea un anti-patrón: cuando hay una demanda difícil de cubrir (pocas personas habilitadas) y la única persona disponible ya tiene horas asignadas, su score cae significativamente. Si hay otro empleado sin horas pero sin la habilidad requerida, ese candidato ni siquiera pasa la validación. Pero si hay dos habilitados y uno ya tiene 3h ese día, el que tiene 0h gana el slot —lo cual es correcto— pero si ese empleado de 0h era el único que podía cubrir una demanda posterior más crítica, se crea un hueco irrecuperable.

**Problema 2 — No hay backtracking ni repair:**

El método `desregistrar()` existe y funciona correctamente, pero **nunca se llama durante el proceso de generación para reorganizar** —solo se usa en el paso POST-RELAX para deshacer exceso de días. No hay ninguna fase que diga: "tengo este hueco, ¿qué asignación existente puedo mover para cubrirlo sin crear otro hueco?".

**Problema 3 — `prom_min` calculado globalmente puede ser engañoso:**

```python
total_demand_min = sum(_seg_min(dm.start, dm.end) * dm.need for dm in demands)
prom_min = total_demand_min / max(1, len(active_emps))
```

Este promedio mezcla demandas de roles especializados con roles generales. Si hay 3 empleados que pueden cubrir JEFE BARRA y 20 que pueden cubrir CAMARERO, el promedio incluye toda la demanda de JEFE BARRA distribuida entre 23 empleados, inflando artificialmente la capacidad percibida para ese rol. Resultado: los multiplicadores de RELAX no escalan correctamente para demandas de roles especializados.

**Problema 4 — `BLOQUE_CORTO_PROVISIONAL` crea un estado de espera que no siempre se resuelve:**

La lógica v5.1 tolera bloques cortos "si el empleado ya tiene algo asignado ese día". Pero si esa demanda corta queda como única del día, no hay ningún mecanismo posterior que intente completarla hasta cumplir `min_duracion_turno_horas`.

**Problema 5 — `ROLE_FALLBACKS_BY_NAME` definido en `agenda.py` pero no integrado en el scorer:**

```python
ROLE_FALLBACKS_BY_NAME = {
    "JEFE BARRA": ["ENLACE", "APOYO ENLACE", "CAMARERO BARRA"],
    ...
}
```

Esta estructura existe pero no se utiliza durante la fase de generación del AI Scheduler para expandir el pool de candidatos cuando no hay cobertura para un rol específico.

**Problema 6 — `SugerenciasMejoraService` (HU 1.3) no desplegada:**

El servicio que analiza gaps y sugiere redistribución existe y está bien diseñado, pero según el propio código: _"aún no está desplegada en ambiente QA"_. Los `suggestion_hints` que inyecta el scorer (`emps_sin_asignacion`, `emps_subutilizados`, `ws_con_gaps`) dependen de este servicio para alimentar el loop siguiente.

### ¿Optimiza localmente pero no globalmente?

**Sí, por diseño.** El greedy asigna el mejor candidato para cada demanda en orden, sin simular el impacto futuro de esa asignación. El sistema no tiene noción de "¿si asigno a A aquí, puedo cubrir la demanda D7 dentro de dos horas?". Esto es el límite fundamental de las heurísticas constructivas puras sin repair.

---

## 3. Clasificación de Restricciones

### Restricciones Duras (nunca violar)

| Nombre                                | Impacto si se incumple                                   | Modelado técnico                                             | ¿Cubierta? |
| ------------------------------------- | -------------------------------------------------------- | ------------------------------------------------------------ | ---------- |
| **Skill/Rol requerido**               | Error de operación (persona sin entrenamiento en puesto) | `emp.can(ws_id)` — roles como `Set`                          | ✅ Sí      |
| **Disponibilidad del empleado**       | Asignación imposible (no está)                           | `emp.available(d, s, e)` con ventanas por DOW + excepciones  | ✅ Sí      |
| **Día libre fijo**                    | Violación de contrato laboral                            | `emp.off(d)` — `day_off: Set[int]`                           | ✅ Sí      |
| **Ausencia registrada**               | Asignación a ausente                                     | `emp.absent_day(d)` — `absent: Set[date]`                    | ✅ Sí      |
| **No solapamiento de turnos**         | Empleado en dos puestos a la vez                         | `_has_overlap()` sobre intervalos del día                    | ✅ Sí      |
| **Descanso mínimo entre turnos (9h)** | Violación legal                                          | `DESC_ENTRE_TURNOS` en `_post_interval_checks`               | ✅ Sí      |
| **Máximo horas semanales**            | Violación de contrato/ley                                | `weekly_hours_ok()` + `LawRestrictions` en BD                | ✅ Sí      |
| **Ventana UserShift**                 | Asignación fuera del horario pactado                     | `_usershift_ok()` con `user_shift_windows`                   | ✅ Sí      |
| **Duración mínima bloque (3h)**       | Turnos económicamente inviables                          | `BLOQUE_CORTO_PROVISIONAL` — relajable bajo cierta condición | ⚠️ Parcial |
| **Máximo bloques por día (2)**        | Exceso de fragmentación                                  | `MAX_BLOQUES` en `_post_interval_checks`                     | ✅ Sí      |

### Restricciones Blandas (deseables, negociables)

| Nombre                              | Impacto si se incumple                           | Modelado técnico                                        | ¿Cubierta?    |
| ----------------------------------- | ------------------------------------------------ | ------------------------------------------------------- | ------------- |
| **Máximo días trabajo semanal (5)** | Fatiga, calidad de vida                          | `MAX_DIAS` — relajable a +1 en RELAX-1                  | ✅ Sí         |
| **Máximo horas por día (9h)**       | Fatiga                                           | `MAX_HORAS_DIA` — relajable a +1h en RELAX-2            | ✅ Sí         |
| **Gap mínimo split (3h)**           | Turnos partidos con gap insuficiente             | `GAP_SPLIT_INSUFICIENTE`                                | ✅ Sí         |
| **Balance de carga semanal**        | Inequidad, desmotivación                         | `_balance_score()` en scorer                            | ✅ Sí         |
| **Balance de carga diaria**         | Un empleado lleva todo el día                    | `_daily_hours_score()` en scorer                        | ✅ Sí         |
| **Continuidad en puesto**           | Eficiencia operativa                             | `s_cont` en scorer (peso 0.04)                          | ✅ Sí         |
| **Afinidad histórica emp-ws**       | Calidad, confort del empleado                    | `_afinidad_emp_ws` extraído de CSV/BD                   | ✅ Sí         |
| **Preferencia por días habituales** | Estabilidad de vida personal                     | `dias_frecuentes` en `PatronEmpWS`                      | ✅ Sí         |
| **Equidad de días trabajados**      | Inequidad                                        | `_days_balance_score()` en scorer                       | ✅ Sí         |
| **Empleados sin asignación**        | Subutilización, conflicto contractual            | `bonus +0.15` si `minutos_semana == 0`                  | ⚠️ Parcial    |
| **Penalización por huecos en ws**   | No genera penalización explícita al solver       | `ws_con_gaps` hints — sin efecto si HU1.3 no desplegada | ❌ Incompleta |
| **Estabilidad del horario**         | Cambios innecesarios semana a semana             | No modelado                                             | ❌ No         |
| **Fallbacks de rol**                | Puesto sin cubrir cuando hay personal compatible | `ROLE_FALLBACKS_BY_NAME` no integrado en scorer         | ❌ No         |

---

## 4. Análisis de Huecos No Funcionales

### Tipología de huecos identificada

**A. Huecos inevitables** (no se pueden corregir con algoritmo):

- Franjas donde la demanda supera la capacidad real de personal habilitado (combinación de skill + disponibilidad + horas contratadas).
- Detectables: el sistema ya hace `[DIAG-WS]` con `n_emps_with_skill` para cada workstation sin cubrir.
- **Acción:** marcarlos explícitamente como `HUECO_ESTRUCTURAL` y reportarlos al administrador.

**B. Huecos corregibles por Repair Engine** (el principal foco de mejora):

- Empleado A asignado en franja F1 pero podría haberse movido a F2 para abrir espacio a Empleado B en F1, cubriendo también F3.
- Demanda D1 cubierta con Empleado A cuando Empleado B (único habilitado para D2) hubiera podido cubrir D1, liberando a A para D2.
- Demandas de rol con fallback: JEFE BARRA no cubierto cuando hay ENLACE disponible.

**C. Huecos causados por mala estrategia algorítmica:**

- **Conflicto balance vs cobertura en demandas especializadas:** el scorer penaliza a empleados con horas aunque sean los únicos habilitados para cierto rol.
- **`prom_min` inflado:** el promedio global sobreestima la capacidad para demandas de roles escasos, desactivando el mecanismo de relajación antes de tiempo.
- **Sugerencias sin retroalimentar:** `ws_con_gaps` hints del scorer no tienen datos reales porque HU 1.3 no está desplegada.

**D. Huecos causados por datos insuficientes o mal parametrizados:**

- Empleados sin roles asignados que podrían ser entrenados (`CAPACITAR_EMPLEADO`).
- Ventanas de disponibilidad demasiado restrictivas para la demanda real.
- `LawRestrictions` con valores que no corresponden al contexto real de cada empleado.

### Patrón más probable del 10% de huecos residual

Con base en el diagnóstico que el propio sistema genera, el patrón más probable es:

```
[DIAG] Rechazos: FUERA_VENTANA: 45, MAX_HORAS_SEMANALES: 38, SIN_SKILL: 22, MAX_DIAS: 18
```

Los primeros dos (`FUERA_VENTANA` y `MAX_HORAS_SEMANALES`) son los candidatos más probables y ambos son atacables con un Repair Engine que redistribuya carga de empleados sobrecargados hacia franjas en huecos.

---

## 5. Propuesta de Mejora Recomendada

### A. Heurística actual → Mantener como generador inicial

El motor actual es la base y no debe tocarse. La propuesta es **envolver el resultado** del generador con capas adicionales que lo mejoren sin modificar su lógica interna.

### B. Gap Analyzer → Ya existe, necesita despliegue y extensión

`explicador_huecos.py` + `sugerencias_mejora.py` ya implementan esto. Lo que falta:

- Desplegar HU 1.3 en producción.
- Agregar al `AnalisisGaps` la distinción entre huecos inevitables y corregibles.
- Alimentar el Repair Engine con la lista de huecos clasificados.

### C. Score Engine → Dos ajustes concretos

El `ScorerCandidatos` ya es sólido. Se necesitan dos cambios quirúrgicos:

**Ajuste 1:** Calcular `prom_min` por grupo de skill, no global:

```python
# En lugar de:
prom_min = total_demand_min / max(1, len(active_emps))

# Calcular por pool de habilidad:
prom_min_by_role = {}
for ws_id in unique_ws_ids:
    emps_with_skill = [e for e in active_emps if e.can(ws_id)]
    demand_for_ws = sum(
        _seg_min(dm.start, dm.end) * dm.need
        for dm in demands if dm.wsid == ws_id
    )
    prom_min_by_role[ws_id] = demand_for_ws / max(1, len(emps_with_skill))
```

**Ajuste 2:** Agregar un término de "presión de cobertura" que suba el score de demandas con pocos candidatos restantes:

```python
# Factor de urgencia: si quedan pocas personas disponibles para este ws, priorizar cobertura
n_remaining_candidates = sum(
    1 for e in emps
    if e.can(dm.wsid) and estados[str(e.id)].minutos_semana < weekly_limit
)
urgency_factor = max(0.0, 1.0 - (n_remaining_candidates / max(1, n_total_qualified)))
score += urgency_factor * 0.30  # Supera el peso de balance cuando es urgente
```

### D. Repair Engine → El componente nuevo más importante

Este es el componente que tiene mayor impacto potencial y menor riesgo. Trabaja **después** de que `AIScheduleGenerator.generar()` termina, con su resultado como entrada.

**Algoritmo base:**

```
Para cada hueco H (demanda sin cubrir):
    1. Buscar empleados habilitados para H pero ya saturados (MAX_HORAS o MAX_DIAS)
    2. Para cada empleado saturado E:
        a. Listar asignaciones de E en la misma semana
        b. Para cada asignación A de E:
           - Verificar si se puede reasignar A a otro empleado E2
           - Verificar que con E2 en A, E queda libre para H
           - Calcular delta de score: score(E en H) + score(E2 en A) vs estado actual
           - Si delta > umbral, ejecutar el swap
    3. Verificar si el hueco H sigue sin cubrir; si no, continuar
    4. Intentar extensión de turno: ¿puede algún empleado ya asignado ese día extender
       su turno para cubrir H? (respetando max_horas_dia y descanso)
```

**Clave de implementación:** El `EstadoEmpleado` ya tiene `desregistrar()` y `registrar()`, que son exactamente las operaciones que necesita el Repair Engine. Solo falta el bucle de evaluación de intercambios.

### E. Solver / Optimization Engine → Evaluar en Fase 5

**Recomendación de solver si se decide avanzar:** **OR-Tools CP-SAT** de Google.

**Por qué CP-SAT sobre las otras opciones:**

- Maneja restricciones mixtas (duras/blandas) con penalizaciones en la función objetivo.
- Escala razonablemente bien hasta ~200 empleados × 7 días × 20 puestos.
- Tiene soporte Python nativo y es open source.
- Permite configurar un tiempo máximo de ejecución y retorna la mejor solución encontrada hasta ese momento (anytime algorithm).
- Algoritmos genéticos y simulated annealing requieren calibración de parámetros que para este dominio es muy costosa.

**No se recomienda todavía** porque el Repair Engine probablemente lleva la cobertura al 95-97% con mucho menos riesgo y complejidad.

### F. IA Explicativa → Ya existe, necesita despliegue

`explicador_huecos.py`, `sugerencias_mejora.py` y el módulo de aprendizaje histórico ya implementan IA explicativa. Lo que sí tiene sentido agregar es un componente LLM ligero (GPT-4o-mini o Claude Haiku) para:

- Generar el texto de `Sugerencia.descripcion` y `acciones_concretas` de forma más natural.
- Resumir el informe de cobertura para el administrador en lenguaje no técnico.

**Lo que NO debe hacer la IA generativa:** tomar decisiones de asignación. Su uso como motor de asignación es inviable: no respeta restricciones duras de forma garantizada, no es determinista y no es auditable.

---

## 6. Diseño Técnico Propuesto

### Componentes existentes (mantener y extender)

| Componente                    | Archivo                    | Responsabilidad                                      | Estado              |
| ----------------------------- | -------------------------- | ---------------------------------------------------- | ------------------- |
| `AIScheduleGenerator`         | `ai_scheduler.py`          | Motor greedy multi-fase                              | ✅ Producción       |
| `ValidadorReglasDuras`        | `ai_scheduler.py`          | Validación de restricciones duras                    | ✅ Producción       |
| `ScorerCandidatos`            | `ai_scheduler.py`          | Scoring de candidatos para asignación                | ✅ Necesita ajustes |
| `ExtractorPatrones`           | `ai_scheduler.py`          | Extracción de patrones históricos                    | ✅ Producción       |
| `ExplicadorHuecos`            | `explicador_huecos.py`     | Categorización y explicación de huecos               | ✅ Producción       |
| `TurnQualityService`          | `puntaje_calidad_turno.py` | Score de calidad por turno (coverage/fairness/rules) | ✅ Producción       |
| `ValidadorReglas`             | `validador_reglas.py`      | Validación post-generación de restricciones          | ✅ Producción       |
| `SugerenciasMejoraService`    | `sugerencias_mejora.py`    | Análisis de gaps y sugerencias accionables           | ⚠️ No desplegado    |
| `AprendizajeHistoricoService` | `aprendizaje_historico.py` | Aprendizaje incremental desde histórico              | ✅ Producción       |

### Componentes nuevos a crear

#### `ScheduleRepairEngine` — nuevo en `services/repair_engine.py`

```python
class ScheduleRepairEngine:
    """
    Responsabilidad: Mejorar el resultado del AIScheduleGenerator
    buscando intercambios y extensiones que cubran huecos sin
    crear nuevas violaciones.

    Entrada:
        - sched: Dict[date, List[Tuple[Emp, Demand]]]  -- resultado de generar()
        - estados: Dict[str, EstadoEmpleado]            -- estados finales
        - coverage_stats: Dict[demand_id, CoverageInfo]
        - remaining: Dict[demand_id, int]               -- slots sin cubrir
        - emps: List[Emp]
        - demands: List[Demand]
        - validador: ValidadorReglasDuras
        - scorer: ScorerCandidatos

    Salida:
        - RepairResult con sched mejorado, estado actualizado y métricas

    Qué parte del problema resuelve:
        - Huecos corregibles (tipo B de la sección 4)
        - Redistribución post-generación sin regenerar desde cero
    """

    def reparar(self, ...) -> RepairResult:
        gaps = self._detectar_huecos(remaining, demands)
        for gap in self._priorizar_gaps(gaps):
            repaired = self._intentar_swap(gap, ...)
            if not repaired:
                repaired = self._intentar_extension(gap, ...)
            if not repaired:
                repaired = self._intentar_fallback_rol(gap, ...)
        return RepairResult(...)
```

#### `ScheduleGapClassifier` — extensión de `explicador_huecos.py`

```python
class ScheduleGapClassifier:
    """
    Responsabilidad: Clasificar cada hueco como inevitable o corregible.

    Entrada: huecos del ExplicadorHuecos + estados de empleados + demands
    Salida: List[ClassifiedGap] con tipo:
            INEVITABLE | CORREGIBLE_SWAP | CORREGIBLE_EXTENSION |
            CORREGIBLE_FALLBACK | DATO_INSUFICIENTE
    """
```

#### `ScheduleScoreAggregator` — nuevo en `services/score_aggregator.py`

```python
class ScheduleScoreAggregator:
    """
    Responsabilidad: Calcular el score global del horario completo
    (no por turno individual como TurnQualityService).

    Entrada: sched, coverage_stats, emps, demands, violations
    Salida: ScheduleScore con descomposición por dimensión

    Dimensiones:
        - cobertura_global: porcentaje de demanda cubierta
        - huecos_criticos: count de huecos inevitables
        - huecos_corregibles: count de huecos atacables por repair
        - equidad_carga: coeficiente de variación de horas por empleado
        - violaciones_duras: count (debe ser 0)
        - violaciones_blandas: count ponderado
        - score_total: 0-100 combinado
    """
```

---

## 7. Contratos de Entrada y Salida

```python
@dataclass
class EmployeeAvailability:
    emp_id: str
    emp_name: str
    available_dow: List[int]                               # Días disponibles (0=Lun, 6=Dom)
    time_windows: Dict[int, List[Tuple[time, time]]]       # Ventanas por DOW
    date_exceptions: Dict[date, List[Tuple[time, time]]]   # Excepciones por fecha
    absent_dates: Set[date]
    absent_reasons: Dict[date, str]
    hired_hours_week: float
    law_apply: bool
    complement_hours: bool


@dataclass
class EmployeePreference:
    emp_id: str
    day_preferences: Dict[int, float]      # DOW → 0.0=no quiere, 1.0=prefiere
    ws_preferences: Dict[str, float]       # ws_id → preferencia
    historical_affinity: Dict[str, PatronEmpWS]


@dataclass
class StaffingDemand:
    id: str
    date: date
    workstation_id: str
    workstation_name: str
    start_time: time
    end_time: time
    required_staff: float   # Puede ser decimal: 1.5 = 1 normal + 1 híbrido
    normal_need: int        # Personas enteras requeridas
    has_hybrid: bool


@dataclass
class ShiftRequirement:
    demand_id: str
    eligible_roles: List[str]      # Rol principal + fallbacks
    shift_type: str                # mañana / tarde / noche / partido
    is_critical: bool              # Nocturno, fin de semana, rol escaso
    available_candidates: int      # Calculado antes de la generación


@dataclass
class GeneratedShift:
    id: str
    date: date
    employee_id: str
    employee_name: str
    workstation_id: str
    workstation_name: str
    start_time: time
    end_time: time
    duration_minutes: int
    observation: str           # BT / C / ABS / ""
    is_hybrid: bool
    demand_id: str
    assignment_score: float    # Score del candidato en el momento de asignación


@dataclass
class ScheduleCandidate:
    token: str
    week_start: date
    week_end: date
    shifts: List[GeneratedShift]
    employee_states: Dict[str, EstadoEmpleado]
    coverage_stats: Dict[str, Any]   # demand_id → {covered, unmet, pct}


@dataclass
class ScheduleScore:
    token: str
    total_score: float          # 0-100 global
    coverage_score: float       # % demanda cubierta
    fairness_score: float       # Equidad de carga (coef. variación)
    rules_score: float          # Restricciones respetadas
    preference_score: float     # Preferencias cumplidas
    coverage_pct: float
    covered_slots: int
    total_slots: int
    critical_gaps: int
    fixable_gaps: int
    structural_gaps: int
    violations_hard: int
    violations_soft: int
    split_shifts_count: int
    employees_assigned: int
    employees_unassigned: int
    repair_delta: float         # Mejora tras repair (0.0 si no se ejecutó)


@dataclass
class ScheduleGap:
    demand_id: str
    date: date
    workstation_id: str
    workstation_name: str
    start_time: time
    end_time: time
    duration_minutes: int
    slots_missing: int
    gap_type: str               # INEVITABLE | CORREGIBLE_SWAP | CORREGIBLE_EXTENSION | CORREGIBLE_FALLBACK
    rejection_reasons: Dict[str, str]      # emp_id → razón
    skill_qualified_employees: List[str]   # Habilitados por skill (aunque saturados)
    available_employees: List[str]         # Disponibles en esa franja


@dataclass
class ScheduleViolation:
    tipo: str           # Del TipoViolacion enum existente
    severidad: str
    employee_id: str
    employee_name: str
    date: date
    detail: str
    actual_value: float
    expected_value: float
    workstation: str


@dataclass
class RepairSuggestion:
    gap_demand_id: str
    repair_type: str                            # SWAP | EXTENSION | FALLBACK_ROLE | RELAX_WINDOW
    description: str
    target_employee_id: str
    displaced_assignment: Optional[GeneratedShift]
    replacement_employee_id: Optional[str]
    score_delta: float                          # Positivo = mejora
    applied: bool
    not_applied_reason: str


@dataclass
class OptimizationResult:
    token: str
    original_score: ScheduleScore
    repaired_score: ScheduleScore
    gaps_before: int
    gaps_after: int
    repairs_attempted: int
    repairs_applied: int
    repair_suggestions: List[RepairSuggestion]
    execution_time_ms: int
    solver_used: bool
    solver_name: Optional[str]
    solver_objective_value: Optional[float]
```

---

## 8. Métricas de Evaluación

```python
# ── MÉTRICAS PRIMARIAS (impacto en operación) ──────────────────────────────
coverage_pct              # % de slots de demanda cubiertos — objetivo: >95%
critical_gaps_count       # Huecos inevitables (sin personal habilitado)
fixable_gaps_count        # Huecos que el repair podría cerrar
hard_violations_count     # Restricciones duras violadas — objetivo: 0

# ── MÉTRICAS DE CALIDAD DE DISTRIBUCIÓN ────────────────────────────────────
fairness_cv               # Coeficiente de variación de horas por empleado (σ/μ) — objetivo: <0.25
hours_assigned_vs_required  # Ratio horas asignadas / horas requeridas por empleado
split_shifts_count        # Número de turnos partidos — objetivo: minimizar
employees_unassigned      # Empleados sin ninguna asignación — objetivo: 0

# ── MÉTRICAS DE REPAIR ENGINE ───────────────────────────────────────────────
repairs_applied           # Número de swaps/extensiones ejecutados
repair_success_rate       # repairs_applied / repairs_attempted — objetivo: >60%
coverage_delta_after_repair  # Mejora de cobertura tras repair — objetivo: >+3%

# ── MÉTRICAS DE RENDIMIENTO ─────────────────────────────────────────────────
generation_time_ms        # Tiempo de generación — objetivo: <10s para semana típica
repair_time_ms            # Tiempo de repair — objetivo: <5s adicionales
total_time_ms             # Tiempo total — objetivo: <15s

# ── MÉTRICAS COMPARATIVAS ───────────────────────────────────────────────────
score_before_repair       # ScheduleScore.total_score antes del repair
score_after_repair        # ScheduleScore.total_score después del repair
regression_vs_baseline    # Comparación contra el mejor horario histórico de esa semana

# ── MÉTRICAS DE DIAGNÓSTICO ─────────────────────────────────────────────────
impossible_detected_correctly  # ¿El sistema identificó correctamente los huecos inevitables?
false_impossible_rate     # Huecos marcados como inevitables que el repair pudo cerrar
```

---

## 9. Estrategia de Implementación por Fases

### Fase 1 — Auditoría y diagnóstico (sin cambios en producción)

**Objetivo:** Entender con precisión de dónde viene el 10% de huecos.

**Cambios técnicos:**

- Activar logging detallado del bloque `[DIAG]` y `[DIAG-WS]` en producción durante 2-4 semanas.
- Crear script de análisis offline que tome los CSVs (`horariogenerado.csv`, `huecos.csv`, `restricionesVioladas.csv`) y calcule la distribución de razones de rechazo.
- Verificar que `_Schedules__202601300806.csv` y el CSV de la BD estén sincronizados como fuente de aprendizaje.

**Riesgos:** Ninguno (solo lectura).

**Criterios de aceptación:**

- Ranking de razones de rechazo con porcentajes (ej: 45% `FUERA_VENTANA`, 30% `MAX_HORAS`).
- Lista de workstations con más huecos recurrentes.
- Identificación del ratio huecos inevitables vs corregibles.

**Pruebas mínimas:** Script de análisis con los CSVs actuales.

**Resultado esperado:** Saber exactamente dónde atacar en Fase 3.

---

### Fase 2 — Despliegue de HU 1.3 + `ScheduleScoreAggregator`

**Objetivo:** Tener visibilidad cuantificada del score global antes de intentar mejorarlo.

**Cambios técnicos:**

- Desplegar `SugerenciasMejoraService` en QA, validar que no afecta BD de producción.
- Implementar `ScheduleScoreAggregator` como servicio adicional (no modifica el flujo existente).
- Agregar endpoint `/api/agenda/score/{token}` que devuelva el `ScheduleScore` del horario generado.

**Riesgos:** La inserción en `ScheduleSuggestions` podría conflictuar con datos existentes — usar `ON CONFLICT DO NOTHING` como hace `TurnQualityService`.

**Criterios de aceptación:**

- Score total disponible en la API para cualquier horario generado.
- `SugerenciasMejoraService` corriendo en QA sin errores.
- `suggestion_hints` alimentando correctamente el scorer de la siguiente generación.

**Pruebas mínimas:**

- Generar horario para semana de prueba → verificar que `/api/agenda/score` devuelve datos.
- Comparar score con 3 horarios históricos del CSV.

**Resultado esperado:** Baseline de score medible. Las siguientes fases tienen métrica de éxito clara.

---

### Fase 3 — Repair Engine básico (swaps + extensiones)

**Objetivo:** Reducir huecos corregibles, mejorar cobertura de 90% → 94-96%.

**Cambios técnicos:**

- Crear `services/repair_engine.py` con `ScheduleRepairEngine`.
- Integrar al final de `generate_ai()` en `agenda.py` (llamada condicional: solo si `coverage < threshold`).
- Implementar primero SWAP (el más impactante), luego EXTENSION, luego FALLBACK_ROLE.
- El Repair Engine recibe el estado final del `AIScheduleGenerator` y lo mejora en su propio ciclo.

**Implementación de SWAP:**

```python
def _intentar_swap(self, gap: ScheduleGap, ...) -> bool:
    candidates_for_gap = [e for e in emps if e.can(gap.workstation_id)]

    for emp in candidates_for_gap:
        estado = estados[str(emp.id)]
        ok, reason = validador.puede_asignar(emp, gap_as_demand, gap.date, estado)
        if ok:
            # Puede cubrir directamente (la generación lo pasó por alto)
            self._asignar(emp, gap_as_demand, ...)
            return True

        if reason in ("MAX_HORAS_SEMANALES", "MAX_DIAS", "MAX_HORAS_DIA"):
            for d, ws, s, e in estado.asignaciones:
                existing_dm = self._find_demand(d, ws, s, e)
                alt_emp = self._mejor_candidato_excluyendo(emp, existing_dm, d, ...)
                if alt_emp:
                    estado_sim = self._simular_desregistro(estado, d, ws, s, e)
                    ok_after, _ = validador.puede_asignar(
                        emp, gap_as_demand, gap.date, estado_sim
                    )
                    if ok_after:
                        self._ejecutar_swap(emp, existing_dm, alt_emp, gap_as_demand, ...)
                        return True
    return False
```

**Riesgos:**

- El swap puede mejorar un hueco pero crear otro. **Mitigación:** validar score global antes/después de cada swap; revertir si el score no mejora.
- Tiempo de ejecución cuadrático en el peor caso. **Mitigación:** limitar a top-20 gaps por criticidad y top-10 candidatos por gap.

**Criterios de aceptación:**

- Cobertura media mejora ≥ 2% sobre el baseline de Fase 2.
- Cero nuevas violaciones de restricciones duras introducidas por el repair.
- `repair_time_ms` < 5000ms para semana típica.

**Resultado esperado:** Cobertura 93-96%. Score global +5 a +8 puntos.

---

### Fase 4 — Simulación y comparación de escenarios

**Objetivo:** Permitir al administrador ver y comparar múltiples variantes del horario.

**Cambios técnicos:**

- Endpoint `/api/agenda/simulate` que acepta parámetros alternativos (relajar ventanas, horas extra, cambiar `min_coverage_pct`).
- `ScheduleSimulationService` que ejecuta el generador + repair con diferentes configuraciones.
- Persistir múltiples candidatos con su `ScheduleScore` para comparación.

**Riesgos:** Carga en BD si se generan muchos candidatos. **Mitigación:** máximo 3 variantes por semana, con TTL de 24h.

**Criterios de aceptación:** El administrador puede comparar 2-3 escenarios con métricas claras.

---

### Fase 5 — Evaluación de OR-Tools CP-SAT

**Objetivo:** Determinar si un solver formal puede mejorar el resultado más allá del repair.

**Cambios técnicos:**

- Instalar `ortools` en el entorno.
- Modelar el problema como CP-SAT para el subconjunto de demandas no cubiertas por el greedy.
- Usar el greedy + repair como solución inicial del solver (warm start).

**Riesgos:**

- Tiempo de modelado alto para semanas complejas.
- Dificultad de mantener el modelo CP sincronizado con cambios de reglas de negocio.
- **Mitigación:** usar CP-SAT solo para el conjunto de huecos residuales (≤10% de demandas), no para todo el horario.

**Criterios de aceptación:** CP-SAT mejora la cobertura ≥ 1% adicional sobre el repair, en tiempo ≤ 30s.

---

### Fase 6 — IA explicativa y asistente de análisis

**Objetivo:** Mejorar la comunicación del resultado al administrador.

**Cambios técnicos:**

- Integrar LLM ligero (API call) en `ExplicadorHuecos` para generar texto natural de los reportes.
- Endpoint `/api/agenda/explain/{token}` que devuelva resumen ejecutivo del horario.

**Riesgos:** Dependencia de API externa; latencia. **Mitigación:** generar explicaciones de forma asíncrona, no bloquear el flujo principal.

---

## 10. Pruebas Necesarias

### Unitarias

```python
# repair_engine_test.py

def test_swap_basico():
    """Empleado A saturado puede ceder un turno a Empleado B para cubrir hueco."""

def test_swap_no_crea_hueco_nuevo():
    """Un swap que cubre un hueco pero crea otro NO debe aplicarse."""

def test_extension_respeta_max_horas_dia():
    """Extender un turno no debe superar max_horas_por_dia."""

def test_repair_con_cero_candidatos_habilitados():
    """Si ningún empleado tiene el skill, el hueco debe marcarse INEVITABLE."""


# scorer_test.py

def test_urgency_factor_supera_balance():
    """Si quedan 0 candidatos disponibles para ws, el score ignora balance."""

def test_prom_min_por_rol_vs_global():
    """prom_min por rol da valor distinto que global para roles especializados."""
```

### Integración

```python
def test_generacion_completa_con_repair():
    """Generar horario → aplicar repair → verificar que coverage >= baseline + 2%."""

def test_score_aggregator_consistente_con_turn_quality():
    """ScheduleScoreAggregator.coverage debe coincidir con suma de TurnQualityService."""

def test_suggestions_retroalimentan_siguiente_generacion():
    """Sugerencias de HU1.3 deben aumentar score de emps_sin_asignacion en siguiente run."""
```

### Casos Límite

```python
def test_demanda_mayor_que_disponibilidad():
    """need=5 con solo 3 empleados habilitados → 3 cubiertos, 2 INEVITABLE."""

def test_preferencias_contradictorias():
    """Dos empleados prefieren mismo día/ws → asignar al de menor carga."""

def test_empleado_disponible_sin_rol():
    """Empleado con disponibilidad total pero sin skill → SIN_SKILL, no FUERA_VENTANA."""

def test_sobrecobertura_y_hueco_simultaneo():
    """ws_A tiene 3 asignados (need=2) y ws_B tiene 0 (need=1) → repair redistribuye."""

def test_turno_partido():
    """Demanda 08-11 + 15-18 → 2 bloques válidos si gap>=3h. Gap 2h → rechazo."""

def test_maximo_horas_semanal():
    """Empleado con 38h contratadas + 36h ya asignadas → solo 2h más disponibles."""

def test_descanso_minimo():
    """Turno hasta 23:00 → siguiente turno no antes de 08:00 del día siguiente."""

def test_empleado_disponibilidad_muy_limitada():
    """Empleado disponible solo martes 9-13h → solo asignable en esa ventana."""
```

### Regresión

```python
def test_regression_vs_csv_baseline():
    """Generar horario con los mismos datos del CSV histórico → coverage >= CSV_baseline."""

def test_score_no_decrece_con_repair():
    """ScheduleScore después del repair SIEMPRE >= score antes del repair."""

def test_hard_violations_siguen_en_cero():
    """El repair NUNCA introduce violaciones de restricciones duras."""
```

### Rendimiento

```python
def test_performance_20_emps_100_demands():
    """Generar + repair en < 10s para 20 empleados y 100 demandas."""

def test_performance_50_emps_300_demands():
    """Generar + repair en < 30s para 50 empleados y 300 demandas."""
```

---

## 11. Riesgos Técnicos

| Riesgo                                                         | Probabilidad                  | Impacto | Mitigación                                                                                          |
| -------------------------------------------------------------- | ----------------------------- | ------- | --------------------------------------------------------------------------------------------------- |
| **Repair introduce violaciones duras**                         | Media                         | Alto    | Validar cada swap con `puede_asignar()` antes de aplicarlo; revertir si falla                       |
| **Tiempo de ejecución cuadrático en repair**                   | Alta                          | Medio   | Limitar a top-N gaps × top-K candidatos; añadir timeout y retornar mejor resultado hasta ese punto  |
| **`prom_min` inflado genera falsos positivos en RELAX**        | Alta                          | Medio   | Implementar el ajuste de `prom_min` por rol en Fase 3                                               |
| **HU 1.3 afecta BD de producción al desplegarse**              | Baja                          | Alto    | Desplegar primero en QA con `ON CONFLICT DO NOTHING` en todos los inserts                           |
| **Score engine no captura todos los escenarios de inequidad**  | Media                         | Bajo    | Agregar `fairness_cv` como métrica de auditoría; no bloquear el deploy por esto                     |
| **IA generativa incumple restricciones**                       | Alta (si se usara como motor) | Crítico | **No usar LLM para asignación**; solo para texto explicativo                                        |
| **Cambios en el scorer rompen comportamiento actual**          | Alta                          | Alto    | Feature flag para nuevo scorer; A/B test en QA durante 2 semanas antes de producción                |
| **Reglas de negocio ambiguas**                                 | Media                         | Medio   | Agregar test de regresión contra CSV histórico antes de cualquier cambio en `REGLAS_DURAS_DEFAULTS` |
| **Datos de entrada inconsistentes (ventanas vacías, horas=0)** | Media                         | Medio   | Los guardias ya existen (`if dur <= 0`, `if hired_hours <= 0`); documentarlos con tests explícitos  |
| **Sobreoptimización del score global a costa de legibilidad**  | Baja                          | Bajo    | Mantener el score descompuesto (coverage/fairness/rules) visible para el administrador              |

---

## 12. Recomendación Final

### Lo que debe hacerse inmediatamente

**1. Corregir el `prom_min` por rol** — es un cambio de ~10 líneas en `ai_scheduler.py` con alto impacto. El promedio global inflado hace que los multiplicadores de RELAX sean demasiado conservadores para roles especializados.

**2. Desplegar `SugerenciasMejoraService` (HU 1.3)** — está listo, solo necesita validación en QA. Los `suggestion_hints` que habilita ya están en el scorer pero sin datos reales.

**3. Activar logging de diagnóstico en producción** — los bloques `[DIAG]` y `[DIAG-WS]` ya existen. Solo hace falta que lleguen a un sistema de monitoreo para tener datos reales del 10% de huecos.

### Lo que debe hacerse en el siguiente sprint

**4. Implementar `ScheduleRepairEngine`** — es el componente de mayor impacto. Usa la infraestructura existente (`desregistrar()`/`registrar()`, `puede_asignar()`, `ScorerCandidatos`) y puede añadir 3-6 puntos de cobertura sin tocar el motor generador.

**5. Implementar `ScheduleScoreAggregator`** — necesario para medir el impacto del repair y de cualquier cambio futuro.

### Lo que NO debe hacerse todavía

- **No integrar OR-Tools:** el motor actual con repair probablemente alcanza 95-96% de cobertura. Un solver formal tiene alto coste de implementación y mantenimiento. Evaluar solo cuando el repair haya sido desplegado y se pueda medir el gap residual.
- **No reemplazar la heurística greedy:** es estable, comprensible y desplegada. Su valor como generador inicial es alto.
- **No usar LLM como motor de asignación:** bajo ninguna circunstancia. Solo para texto explicativo post-generación.
- **No intentar alcanzar el 100%:** una fracción de los huecos son inevitables (skill + disponibilidad insuficiente). El objetivo realista es identificarlos correctamente y comunicarlos, no eliminarlos.

### Entregable técnico de este análisis

El resultado concreto que debe salir de este análisis es un **`services/repair_engine.py`** con:

- `ScheduleRepairEngine.reparar()` implementando swap y extensión.
- `ScheduleGapClassifier` integrando la clasificación `INEVITABLE | CORREGIBLE_*`.
- Tests unitarios para los 8 casos límite definidos en la sección 10.
- Un `ScheduleScoreAggregator` con la métrica `coverage_delta_after_repair` como KPI principal.

La primera señal de que el repair funciona es: el número de huecos en `restricionesVioladas.csv` y `huecos.csv` baja ≥ 30% en las primeras 2 semanas de producción.

---

### Información faltante que debe recolectarse

| Dato                                                                 | Por qué se necesita                                                                                             | Cómo obtenerlo                                                               |
| -------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------- |
| Distribución real de razones de rechazo                              | Saber si el 10% es mayormente `FUERA_VENTANA`, `MAX_HORAS` o `SIN_SKILL` determina qué tipo de repair priorizar | Activar logging `[DIAG]` en producción 2 semanas                             |
| Número de workstations con skill escaso (1-2 empleados)              | Determinar si los huecos son inevitables por falta estructural de personal                                      | `SELECT ws_id, COUNT(emp_id) FROM emp_roles GROUP BY ws_id HAVING COUNT < 3` |
| Tiempo de ejecución actual del generador                             | Para establecer SLA del repair                                                                                  | Agregar `time.time()` al inicio/fin de `generar()`                           |
| Ratio de huecos que se repiten semana a semana en las mismas franjas | Distinguir huecos estructurales de eventuales                                                                   | Cruzar `huecos.csv` de varias semanas por `(workstation, dow, hora)`         |
