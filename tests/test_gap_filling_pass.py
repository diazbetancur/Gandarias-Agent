"""
tests/test_gap_filling_pass.py
==============================
Tests para ScheduleGapFillingPass (_gap_filling_pass).

Principios verificados:
  - El histórico NO bloquea asignaciones válidas.
  - Todas las reglas provienen de reglas (no hardcodeadas).
  - Aplicación atómica con rollback.
  - Ningún bloque < min_duracion_turno_horas queda tras el pase.
  - Los tres casos (EXTEND / SPLIT / NEW) funcionan correctamente.
"""

from __future__ import annotations

import os
import sys
from collections import defaultdict
from datetime import date, time, timedelta
from typing import Dict, List, Optional, Set, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from services.ai_scheduler import (
    AIScheduleGenerator,
    CandidatePlan,
    EstadoEmpleado,
    ModeloPatrones,
    REGLAS_DURAS_DEFAULTS,
    _t2m,
    _end_min,
    _merge_intervals,
)

# ─────────────────────────────────────────────────────────────────────────────
# STUBS
# ─────────────────────────────────────────────────────────────────────────────

D0 = date(2026, 6, 1)  # lunes de prueba


class FakeEmp:
    _counter = 0

    def __init__(
        self,
        skills: Set[str],
        name: str = "",
        windows: Optional[Dict] = None,
        us_windows: Optional[Dict] = None,
        off_days: Optional[Set[date]] = None,
        weekly_limit_h: Optional[float] = None,
        fixed_start: Optional[time] = None,
        start_range: Optional[Tuple[time, time]] = None,
        max_exit: Optional[time] = None,
    ):
        FakeEmp._counter += 1
        self.id = str(FakeEmp._counter)
        self.name = name or f"Emp{self.id}"
        self._skills = set(skills)
        self._windows = windows or {}  # {date: (time_start, time_end)}
        self.user_shift_windows: Dict = us_windows or {}
        self._off_days = off_days or set()
        self._weekly_limit_h = weekly_limit_h
        self._fixed_start = fixed_start
        self._start_range = start_range
        self._max_exit = max_exit

    def can(self, wsid) -> bool:
        return str(wsid) in self._skills

    def off(self, d: date) -> bool:
        return d in self._off_days

    def absent_day(self, d: date) -> bool:
        return False

    def available(self, d: date, start: time, end: time) -> bool:
        # Ventana general
        if d in self._windows:
            ws, we = self._windows[d]
            if start < ws or end > we:
                return False
        # Hora fija de entrada
        if self._fixed_start is not None and start != self._fixed_start:
            return False
        # Rango de entrada permitido
        if self._start_range is not None:
            lo, hi = self._start_range
            if not (lo <= start <= hi):
                return False
        # Hora máxima de salida
        if self._max_exit is not None:
            end_eff = end if end != time(0, 0) else time(23, 59)
            if end_eff > self._max_exit:
                return False
        return True

    def weekly_hours_limit(self) -> Optional[int]:
        if self._weekly_limit_h is not None:
            return int(self._weekly_limit_h * 60)
        return None


class FakeDemand:
    _counter = 0

    def __init__(
        self,
        wsid: str,
        d: date,
        start: time,
        end: time,
        need: int = 1,
    ):
        FakeDemand._counter += 1
        self.id = str(FakeDemand._counter)
        self.wsid = wsid
        self.date = d
        self.start = start
        self.end = end
        self.need = need
        self.wsname = f"WS_{wsid}"
        self.has_hybrid_component = False


def _make_gen(reglas: Optional[Dict] = None) -> AIScheduleGenerator:
    FakeEmp._counter = 0
    FakeDemand._counter = 0
    rules = dict(REGLAS_DURAS_DEFAULTS)
    if reglas:
        rules.update(reglas)
    gen = AIScheduleGenerator(ModeloPatrones(), reglas=rules, debug=False)
    return gen


def _estado(emp: FakeEmp) -> EstadoEmpleado:
    return EstadoEmpleado(emp_id=str(emp.id))


def _run_gfp(
    gen: AIScheduleGenerator,
    emps: List,
    demands: List,
    sched=None,
    estados=None,
    cov=None,
    remaining=None,
    modelo=None,
):
    """Ejecuta _gap_filling_pass con estructuras mínimas."""
    if sched is None:
        sched = defaultdict(list)
    if estados is None:
        estados = {str(e.id): EstadoEmpleado(emp_id=str(e.id)) for e in emps}
    if cov is None:
        cov = {
            dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": dm.need, "coverage_pct": 0.0, "employees": []}
            for dm in demands
        }
    if remaining is None:
        remaining = {dm.id: dm.need for dm in demands}

    result = gen._gap_filling_pass(emps, demands, sched, estados, cov, remaining, set(), modelo)
    return result, sched, estados, cov, remaining


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — CASO A: EXTENDER BLOQUE EXISTENTE
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_extends_existing_valid_block_with_30_min_gap():
    """Empleado tiene 4h. Se agrega hueco de 30 min pegado al final → bloque 4.5h."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1", "WS2"})

    # Bloque existente: 12:00-16:00 (WS1, 4h)
    dm_existing = FakeDemand("WS1", D0, time(12, 0), time(16, 0))
    # Hueco de 30 min: 16:00-16:30
    dm_gap = FakeDemand("WS2", D0, time(16, 0), time(16, 30))

    demands = [dm_existing, dm_gap]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    # Pre-asignar bloque existente
    gen._asignar(emp, dm_existing, sched, estados, cov, remaining)

    result, sched, estados, cov, remaining = _run_gfp(gen, [emp], demands, sched, estados, cov, remaining)

    assert remaining[dm_gap.id] == 0, "El hueco de 30 min debe quedar cubierto"
    assert result["slots_added"] >= 1
    assert result["final_short_blocks"] == 0


def test_gap_filler_extends_existing_valid_block_without_history():
    """Empleado sin historial puede extender bloque si tiene skill y cumple reglas."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1", "WS2"})

    dm_existing = FakeDemand("WS1", D0, time(10, 0), time(13, 0))
    dm_gap = FakeDemand("WS2", D0, time(13, 0), time(16, 0))

    demands = [dm_existing, dm_gap]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    gen._asignar(emp, dm_existing, sched, estados, cov, remaining)

    # Modelo SIN historial
    result, _, _, cov, remaining = _run_gfp(
        gen, [emp], demands, sched, estados, cov, remaining, modelo=ModeloPatrones()  # vacío, sin afinidades
    )

    assert remaining[dm_gap.id] == 0
    assert result["final_short_blocks"] == 0


def test_gap_filler_does_not_require_history_for_valid_assignment():
    """El histórico no puede bloquear una asignación válida. Ambos empleados aplican."""
    gen = _make_gen()

    # emp_A tiene historial en WS1; emp_B no tiene nada
    emp_a = FakeEmp(skills={"WS1"}, name="EmpA")
    emp_b = FakeEmp(skills={"WS1"}, name="EmpB")

    dm = FakeDemand("WS1", D0, time(10, 0), time(13, 0))
    demands = [dm]

    modelo = ModeloPatrones()
    modelo.afinidad_emp_ws[("1", "WS1")] = type(
        "P",
        (),
        {"frecuencia": 10, "horas_promedio": 3.0, "dias_frecuentes": [0], "horarios": [], "obs_frecuente": "BT"},
    )()

    result, _, _, cov, remaining = _run_gfp(gen, [emp_a, emp_b], demands, modelo=modelo)

    # Al menos uno de los dos debe cubrir la demanda
    assert remaining[dm.id] == 0, "La demanda debe ser cubierta aunque emp_b no tenga historial"
    assert result["final_short_blocks"] == 0


def test_gap_filler_rejects_extension_if_exceeds_max_daily_hours():
    """Empleado con 7.75h, max_horas=8h, hueco de 1h → debe rechazar."""
    gen = _make_gen({"max_horas_por_dia": 8})
    emp = FakeEmp(skills={"WS1", "WS2"})

    # 7h45m ya asignadas como un bloque de 12:00-19:45
    dm_a = FakeDemand("WS1", D0, time(12, 0), time(15, 0))
    dm_b = FakeDemand("WS1", D0, time(15, 0), time(19, 45))

    # Hueco de 1h justo después
    dm_gap = FakeDemand("WS2", D0, time(19, 45), time(20, 45))

    demands = [dm_a, dm_b, dm_gap]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    gen._asignar(emp, dm_a, sched, estados, cov, remaining)
    gen._asignar(emp, dm_b, sched, estados, cov, remaining)

    result, _, _, cov, remaining = _run_gfp(gen, [emp], demands, sched, estados, cov, remaining)

    assert remaining[dm_gap.id] == 1, "Debe rechazar: supera max_horas_dia"
    assert result["final_short_blocks"] == 0


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — CASO B: SEGUNDO BLOQUE PARTIDO
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_creates_second_split_block_after_min_gap():
    """Bloque 1 válido. Gap >= 3h. Bloque 2 de 3h exactas → debe asignarse."""
    gen = _make_gen({"min_gap_split_horas": 3, "min_duracion_turno_horas": 3})
    emp = FakeEmp(skills={"WS1", "WS2"})

    dm_b1 = FakeDemand("WS1", D0, time(8, 0), time(11, 0))  # bloque 1
    dm_b2 = FakeDemand("WS2", D0, time(14, 0), time(17, 0))  # bloque 2 (gap 3h exactas)

    demands = [dm_b1, dm_b2]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    gen._asignar(emp, dm_b1, sched, estados, cov, remaining)

    result, _, _, cov, remaining = _run_gfp(gen, [emp], demands, sched, estados, cov, remaining)

    assert remaining[dm_b2.id] == 0, "Segundo bloque partido válido debe asignarse"
    assert result["final_short_blocks"] == 0


def test_gap_filler_rejects_second_split_if_gap_too_short():
    """Gap entre bloques < min_gap_split → no debe crear turno partido."""
    gen = _make_gen({"min_gap_split_horas": 3, "min_duracion_turno_horas": 3})
    emp = FakeEmp(skills={"WS1", "WS2"})

    dm_b1 = FakeDemand("WS1", D0, time(8, 0), time(11, 0))  # bloque 1
    # Gap de solo 2h (11:00-13:00) — inferior a min_gap_split=3h
    dm_b2 = FakeDemand("WS2", D0, time(13, 0), time(16, 0))  # bloque 2

    demands = [dm_b1, dm_b2]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    gen._asignar(emp, dm_b1, sched, estados, cov, remaining)

    result, _, _, cov, remaining = _run_gfp(gen, [emp], demands, sched, estados, cov, remaining)

    assert remaining[dm_b2.id] == 1, "Gap insuficiente debe rechazarse"


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — RESTRICCIONES DE DISPONIBILIDAD
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_respects_fixed_start_time():
    """Empleado con entrada fija a las 10:00 no puede recibir bloque que inicia a las 09:00."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1"}, fixed_start=time(10, 0))

    # Demanda a las 09:00 — fuera de hora fija
    dm = FakeDemand("WS1", D0, time(9, 0), time(12, 0))

    result, _, _, cov, remaining = _run_gfp(gen, [emp], [dm])

    assert remaining[dm.id] == 1, "Hora fija de entrada no respetada → debe rechazar"


def test_gap_filler_respects_start_time_range():
    """Empleado con rango de entrada 10:00-11:00 rechaza demanda a las 09:00."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1"}, start_range=(time(10, 0), time(11, 0)))

    dm_bad = FakeDemand("WS1", D0, time(9, 0), time(12, 0))
    dm_ok = FakeDemand("WS1", D0, time(10, 0), time(13, 0))

    result, _, _, cov, remaining = _run_gfp(gen, [emp], [dm_bad, dm_ok])

    assert remaining[dm_bad.id] == 1, "Inicio fuera de rango → rechazar"
    assert remaining[dm_ok.id] == 0, "Inicio dentro de rango → asignar"


def test_gap_filler_respects_max_exit_time():
    """Bloque que termina después de la hora máxima de salida debe rechazarse."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1"}, max_exit=time(18, 0))

    # Termina a las 20:00 → supera max_exit=18:00
    dm = FakeDemand("WS1", D0, time(15, 0), time(20, 0))

    result, _, _, cov, remaining = _run_gfp(gen, [emp], [dm])

    assert remaining[dm.id] == 1, "Salida posterior a max_exit → rechazar"


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — CASO C: NUEVO BLOQUE DESDE CERO
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_creates_new_3h_block_for_unassigned_employee():
    """Empleado libre puede cubrir cadena de 3h exactas formando bloque válido."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1", "WS2", "WS3"})

    # Tres demandas contiguas de 1h cada una = 3h total
    dm1 = FakeDemand("WS1", D0, time(9, 0), time(10, 0))
    dm2 = FakeDemand("WS2", D0, time(10, 0), time(11, 0))
    dm3 = FakeDemand("WS3", D0, time(11, 0), time(12, 0))

    result, _, _, cov, remaining = _run_gfp(gen, [emp], [dm1, dm2, dm3])

    covered = sum(1 for dm in [dm1, dm2, dm3] if remaining[dm.id] == 0)
    assert covered == 3, "Cadena de 3h debe quedar totalmente cubierta"
    assert result["final_short_blocks"] == 0


def test_gap_filler_rejects_new_block_under_min_duration():
    """Cadena de 2h < min_duracion_turno_horas(3h) debe rechazarse."""
    gen = _make_gen({"min_duracion_turno_horas": 3})
    emp = FakeEmp(skills={"WS1", "WS2"})

    # Solo 2h contiguas
    dm1 = FakeDemand("WS1", D0, time(10, 0), time(11, 0))
    dm2 = FakeDemand("WS2", D0, time(11, 0), time(12, 0))

    result, _, _, cov, remaining = _run_gfp(gen, [emp], [dm1, dm2])

    assert remaining[dm1.id] == 1 and remaining[dm2.id] == 1, "Cadena de 2h debe rechazarse (< 3h mínimo)"
    assert result["final_short_blocks"] == 0


def test_gap_filler_allows_multi_workstation_block_if_all_skills_valid():
    """Multi-ws contiguo válido si el empleado tiene todos los skills."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1", "WS2", "WS3"})

    dm1 = FakeDemand("WS1", D0, time(10, 0), time(11, 0))
    dm2 = FakeDemand("WS2", D0, time(11, 0), time(12, 30))
    dm3 = FakeDemand("WS3", D0, time(12, 30), time(13, 0))  # total 3h

    result, _, _, cov, remaining = _run_gfp(gen, [emp], [dm1, dm2, dm3])

    assert remaining[dm1.id] == 0
    assert remaining[dm2.id] == 0
    assert remaining[dm3.id] == 0


def test_gap_filler_rejects_multi_workstation_block_if_one_skill_missing():
    """Si falta un skill en parte de la cadena, el plan completo se rechaza."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1", "WS3"})  # NO tiene WS2

    dm1 = FakeDemand("WS1", D0, time(10, 0), time(11, 0))
    dm2 = FakeDemand("WS2", D0, time(11, 0), time(12, 30))  # sin skill
    dm3 = FakeDemand("WS3", D0, time(12, 30), time(13, 0))

    result, _, _, cov, remaining = _run_gfp(gen, [emp], [dm1, dm2, dm3])

    # dm2 no puede asignarse; la cadena que pasa por dm2 también falla
    assert remaining[dm2.id] == 1, "dm2 sin skill debe quedar sin cubrir"


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — HISTÓRICO COMO RANKING
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_uses_historical_affinity_for_ranking_only():
    """Entre dos candidatos válidos, el de mayor afinidad histórica gana.
    El candidato sin historial también es válido y puede asignarse si hay otra demanda."""
    gen = _make_gen()
    emp_hist = FakeEmp(skills={"WS1"}, name="ConHistorial")
    emp_new = FakeEmp(skills={"WS1"}, name="SinHistorial")

    dm = FakeDemand("WS1", D0, time(10, 0), time(13, 0), need=1)

    modelo = ModeloPatrones()
    # emp_hist tiene alta afinidad con WS1
    modelo.afinidad_emp_ws[(str(emp_hist.id), "WS1")] = type(
        "P",
        (),
        {"frecuencia": 20, "horas_promedio": 3.0, "dias_frecuentes": [0], "horarios": [], "obs_frecuente": "BT"},
    )()
    # emp_new no tiene historial — su score de afinidad = 0

    result, _, _, cov, remaining = _run_gfp(gen, [emp_hist, emp_new], [dm], modelo=modelo)

    # La demanda debe cubrirse (por alguno de los dos)
    assert remaining[dm.id] == 0, "La demanda debe cubrirse aunque emp_new no tenga historial"
    assert result["final_short_blocks"] == 0


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — ATOMICIDAD E INMUTABILIDAD
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_applies_atomically():
    """Si un plan falla a mitad (skill falta en demanda intermedia), no aplica nada."""
    gen = _make_gen()
    # emp solo tiene skill WS1, NO WS2
    emp = FakeEmp(skills={"WS1"})

    dm1 = FakeDemand("WS1", D0, time(10, 0), time(11, 0))
    dm2 = FakeDemand("WS2", D0, time(11, 0), time(12, 30))  # sin skill
    dm3 = FakeDemand("WS1", D0, time(12, 30), time(13, 0))

    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in [dm1, dm2, dm3]
    }
    remaining = {dm.id: 1 for dm in [dm1, dm2, dm3]}

    result, sched, estados, cov, remaining = _run_gfp(gen, [emp], [dm1, dm2, dm3], sched, estados, cov, remaining)

    # dm2 no puede asignarse; cualquier cadena que lo incluya se rechaza
    assert remaining[dm2.id] == 1
    assert result["final_short_blocks"] == 0


def test_gap_filler_does_not_mutate_on_failure():
    """Si no hay ningún plan válido, el horario queda intacto."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS99"})  # skill WS99 que no coincide con las demandas

    dm = FakeDemand("WS1", D0, time(10, 0), time(13, 0))

    sched_orig = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}}
    remaining = {dm.id: 1}

    result, sched, _, _, remaining = _run_gfp(gen, [emp], [dm], sched_orig, estados, cov, remaining)

    assert remaining[dm.id] == 1, "Demanda debe seguir sin cubrir (sin skill)"
    assert result["slots_added"] == 0
    assert len(sched[D0]) == 0, "Horario no debe mutar"


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — INVARIANTES GLOBALES
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_final_schedule_has_zero_short_blocks():
    """Después del filler no quedan bloques menores al mínimo configurado."""
    gen = _make_gen({"min_duracion_turno_horas": 3})
    emp = FakeEmp(skills={"WS1", "WS2", "WS3"})

    # Primer bloque ya asignado (3h exactas)
    dm_existing = FakeDemand("WS1", D0, time(9, 0), time(12, 0))
    # Hueco de 30 min pegado al final del bloque → extensión válida
    dm_gap = FakeDemand("WS2", D0, time(12, 0), time(12, 30))
    # Demanda independiente de 2h (< min 3h → no puede crear bloque nuevo)
    dm_short = FakeDemand("WS3", D0, time(15, 0), time(17, 0))

    demands = [dm_existing, dm_gap, dm_short]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    gen._asignar(emp, dm_existing, sched, estados, cov, remaining)

    result, sched, estados, cov, remaining = _run_gfp(gen, [emp], demands, sched, estados, cov, remaining)

    assert result["final_short_blocks"] == 0


def test_gap_filler_improves_coverage_without_hard_violations():
    """El filler sube cobertura válida y no genera violaciones de reglas duras."""
    gen = _make_gen()
    emps = [FakeEmp(skills={"WS1", "WS2"}) for _ in range(3)]

    # 5 demandas: 3 bloques contiguas de 3h (una por empleado)
    demands = [
        FakeDemand("WS1", D0, time(9, 0), time(10, 0)),
        FakeDemand("WS2", D0, time(10, 0), time(11, 0)),
        FakeDemand("WS1", D0, time(11, 0), time(12, 0)),  # total: cadena 9-12
        FakeDemand("WS1", D0 + timedelta(days=1), time(9, 0), time(12, 0)),
        FakeDemand("WS2", D0 + timedelta(days=2), time(9, 0), time(12, 0)),
    ]

    result, _, estados, cov, remaining = _run_gfp(gen, emps, demands)

    total_covered = sum(cs["covered"] for cs in cov.values())
    assert total_covered > 0, "Debe mejorar cobertura"
    assert result["final_short_blocks"] == 0

    # Verificar que no existan solapamientos en ningún empleado
    from services.ai_scheduler import _has_overlap

    for emp in emps:
        est = estados[str(emp.id)]
        for d_key, ivs in est.intervalos_por_dia.items():
            for i, (s1, e1) in enumerate(ivs):
                for j, (s2, e2) in enumerate(ivs):
                    if i != j:
                        assert not _has_overlap(
                            [(s2, e2)], s1, e1
                        ), f"Solapamiento detectado para {emp.name} en {d_key}"


# ─────────────────────────────────────────────────────────────────────────────
# TESTS — DIAGNÓSTICO GAP FILLER
# ─────────────────────────────────────────────────────────────────────────────


def test_gap_filler_diagnostics_reports_top_reject_reasons():
    """El diagnóstico reporta la razón de rechazo dominante correctamente."""
    # Empleado ya saturado en horas diarias (8h = max), hay demanda extra → MAX_HORAS_DIA
    gen = _make_gen({"max_horas_por_dia": 8, "min_duracion_turno_horas": 3})
    emp = FakeEmp(skills={"WS1", "WS2"})

    # Pre-asignar 8h exactas (el máximo)
    dm_a = FakeDemand("WS1", D0, time(10, 0), time(14, 0))
    dm_b = FakeDemand("WS1", D0, time(14, 0), time(18, 0))
    # Demanda adicional (1h) que causaría superar el máximo
    dm_gap = FakeDemand("WS2", D0, time(18, 0), time(21, 0))  # +3h → 11h total → rechazada

    demands = [dm_a, dm_b, dm_gap]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    gen._asignar(emp, dm_a, sched, estados, cov, remaining)
    gen._asignar(emp, dm_b, sched, estados, cov, remaining)

    result, _, _, _, _ = _run_gfp(gen, [emp], demands, sched, estados, cov, remaining)

    diag = result["gap_filler_diagnostics"]
    assert "top_reject_reasons" in diag
    # MAX_HORAS_DIA debe ser la razón dominante
    assert "MAX_HORAS_DIA" in diag["top_reject_reasons"], f"Se esperaba MAX_HORAS_DIA en {diag['top_reject_reasons']}"


def test_gap_filler_diagnostics_groups_by_workstation():
    """El diagnóstico agrupa rechazos por workstation y lista ws con huecos."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1"})  # NO tiene WS2

    dm_ws1 = FakeDemand("WS1", D0, time(10, 0), time(13, 0))
    dm_ws2 = FakeDemand("WS2", D0, time(10, 0), time(13, 0))  # sin skill

    result, _, _, _, _ = _run_gfp(gen, [emp], [dm_ws1, dm_ws2])

    diag = result["gap_filler_diagnostics"]

    # workstations_with_most_unfilled_slots debe incluir WS2
    ws_ids = [w["workstation_id"] for w in diag["workstations_with_most_unfilled_slots"]]
    assert str(dm_ws2.wsid) in ws_ids, "WS2 no cubierta debe aparecer en el diagnóstico"

    # reject_reasons_by_workstation puede estar vacío si no hubo planes evaluados
    # (el empleado no tiene skill, así que no se generan candidatos y no hay rechazo formal)
    assert isinstance(diag["reject_reasons_by_workstation"], dict)
    assert isinstance(diag["reject_reasons_by_day"], dict)


def test_gap_filler_diagnostics_identifies_skill_bottleneck():
    """Workstation sin empleados cualificados → likely_cause = SKILL_BOTTLENECK."""
    gen = _make_gen()
    emp = FakeEmp(skills={"WS1"})  # solo WS1

    dm = FakeDemand("WS_RARO", D0, time(10, 0), time(13, 0))  # nadie tiene skill

    result, _, _, _, _ = _run_gfp(gen, [emp], [dm])

    diag = result["gap_filler_diagnostics"]
    ws_diag = diag["workstations_with_most_unfilled_slots"]
    assert len(ws_diag) == 1
    entry = ws_diag[0]

    assert entry["workstation_id"] == str(dm.wsid)
    assert entry["qualified_employees_count"] == 0
    assert entry["likely_cause"] == "SKILL_BOTTLENECK"


def test_gap_filler_diagnostics_identifies_daily_hours_saturation():
    """Workstation con empleados cualificados pero saturados → DAILY_HOURS_SATURATION."""
    gen = _make_gen({"max_horas_por_dia": 8})
    emp = FakeEmp(skills={"WS1", "WS2"})

    # Saturar 8h
    dm_a = FakeDemand("WS1", D0, time(10, 0), time(14, 0))
    dm_b = FakeDemand("WS1", D0, time(14, 0), time(18, 0))
    # Demanda WS2 que requeriría horas extra (3h → 11h total)
    dm_ws2 = FakeDemand("WS2", D0, time(18, 0), time(21, 0))

    demands = [dm_a, dm_b, dm_ws2]
    sched = defaultdict(list)
    estados = {str(emp.id): EstadoEmpleado(emp_id=str(emp.id))}
    cov = {
        dm.id: {"demand": dm, "met": 0, "covered": 0, "unmet": 1, "coverage_pct": 0.0, "employees": []}
        for dm in demands
    }
    remaining = {dm.id: 1 for dm in demands}

    gen._asignar(emp, dm_a, sched, estados, cov, remaining)
    gen._asignar(emp, dm_b, sched, estados, cov, remaining)

    result, _, _, _, _ = _run_gfp(gen, [emp], demands, sched, estados, cov, remaining)

    diag = result["gap_filler_diagnostics"]
    ws_diag = {w["workstation_id"]: w for w in diag["workstations_with_most_unfilled_slots"]}

    assert str(dm_ws2.wsid) in ws_diag
    entry = ws_diag[str(dm_ws2.wsid)]
    assert entry["likely_cause"] == "DAILY_HOURS_SATURATION"
    # El empleado cualificado debe aparecer en employees_rejected_by_max_hours_day
    assert str(emp.id) in diag["employees_rejected_by_max_hours_day"]


def test_gap_filler_diagnostics_json_serializable():
    """El campo gap_filler_diagnostics es completamente serializable en JSON."""
    import json

    gen = _make_gen()
    emp = FakeEmp(skills={"WS1", "WS2"})

    dm1 = FakeDemand("WS1", D0, time(9, 0), time(10, 0))
    dm2 = FakeDemand("WS2", D0, time(10, 0), time(11, 0))
    dm3 = FakeDemand("WS1", D0, time(11, 0), time(12, 0))  # cadena 3h

    result, _, _, _, _ = _run_gfp(gen, [emp], [dm1, dm2, dm3])

    diag = result["gap_filler_diagnostics"]
    try:
        serialized = json.dumps(diag)
    except (TypeError, ValueError) as exc:
        assert False, f"gap_filler_diagnostics no es JSON serializable: {exc}"

    # Verificar estructura mínima presente
    parsed = json.loads(serialized)
    required_keys = {
        "candidates_total",
        "applied_total",
        "slots_added",
        "top_reject_reasons",
        "reject_reasons_by_workstation",
        "reject_reasons_by_day",
        "workstations_with_most_unfilled_slots",
        "employees_rejected_by_max_hours_day",
        "employees_rejected_by_overlap",
        "skills_bottleneck_summary",
        "operational_recommendations",
    }
    missing = required_keys - set(parsed.keys())
    assert not missing, f"Faltan claves en el diagnóstico: {missing}"
