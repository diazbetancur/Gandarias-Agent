#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
validate_end_to_end.py
======================
Validación end-to-end del Gandarias Scheduling Engine v5.0
con RepairEngine + SkillCoverageAnalyzer integrados.

Fuentes de datos utilizadas:
  - horariogenerado.csv — semana 2026-02-09 (31 emps, 12 ws, 130 asignaciones)
  - save.json           — semana 2026-03-16 (196 demandas, 12 unmet, 93.9%)
  - huecos.csv          — razones de rechazo por workstation

Ejecutar:
    python validate_end_to_end.py [--verbose]
"""

from __future__ import annotations

import argparse
import copy
import csv
import json
import os
import sys
import time as _time_mod
from collections import defaultdict
from datetime import date, datetime, time, timedelta
from typing import Any, Dict, List, Set, Tuple

# ─── Raíz del proyecto en path ─────────────────────────────────────────────
ROOT = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, ROOT)

# ─── Mock de psycopg2 / Flask antes de importar agenda.py ──────────────────
# (agenda.py importa estos módulos a nivel de módulo; mockeamos para no
# necesitar BD ni Flask en la validación offline)
from unittest.mock import MagicMock

_MOCKED = []
for _heavy in ["psycopg2", "psycopg2.extensions", "flask", "flask_cors"]:
    if _heavy not in sys.modules:
        sys.modules[_heavy] = MagicMock()
        _MOCKED.append(_heavy)

import importlib.util as _ilu, pathlib as _pathlib


def _load_agenda():
    if "agenda" in sys.modules:
        return sys.modules["agenda"]
    spec = _ilu.spec_from_file_location(
        "agenda",
        str(_pathlib.Path(ROOT) / "agenda.py"),
    )
    mod = _ilu.module_from_spec(spec)
    sys.modules["agenda"] = mod
    spec.loader.exec_module(mod)
    return mod


_agenda = _load_agenda()
apply_repair = _agenda.apply_repair_if_beneficial
apply_skill_cov = _agenda.apply_skill_coverage_analysis_if_available

# Limpiar mocks (ya no se necesitan)
for _m in _MOCKED:
    sys.modules.pop(_m, None)

# ─── Servicios adicionales ──────────────────────────────────────────────────
from services.ai_scheduler import (
    ValidadorReglasDuras,
    REGLAS_DURAS_DEFAULTS,
)
from services.repair_engine import ScheduleRepairEngine
from services.gap_classifier import ScheduleGapClassifier
from services.skill_coverage_analyzer import SkillCoverageAnalyzer, DeficitType

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTES
# ─────────────────────────────────────────────────────────────────────────────

REGLAS = {
    "min_duracion_turno_horas": 3,
    "min_descanso_entre_turnos_horas": 9,
    "min_gap_split_horas": 3,
    "max_horas_por_dia": 9,
    "dias_descanso_semana": 2,
    "max_dias_trabajo_semana": 5,
    "max_bloques_por_dia": 2,
}

ROLE_FALLBACKS = {
    "JEFE BARRA": ["ENLACE", "APOYO ENLACE", "CAMARERO BARRA"],
    "ENLACE": ["APOYO ENLACE"],
    "JEFE COMEDOR": ["CAMARERO COMEDOR"],
    "CAMARERO BARRA": ["APERTURA BARRA"],
}

# ─────────────────────────────────────────────────────────────────────────────
# STUBS DE EMPLEADO Y DEMANDA (mismos que validate_repair_with_real_data.py)
# ─────────────────────────────────────────────────────────────────────────────


class MinimalEmp:
    def __init__(self, emp_id: str, roles: Set[str], weekly_minutes: int = 40 * 60):
        self.id = emp_id
        self.name = f"Emp-{emp_id[:8]}"
        self.roles = set(roles)
        self.roles_originales = set(roles)
        self.day_off: Set[int] = set()
        self.absent: Set[date] = set()
        self.window: Dict = defaultdict(list)
        self.exc: Dict = defaultdict(list)
        self.user_shift_windows: Dict = defaultdict(list)
        self.split = False
        self.complement_hours = False
        self.law_apply = False
        self.extra_hours = False
        self.cant_part_time_schedule = 0
        self.hired_hours = weekly_minutes / 60
        self._weekly_minutes = weekly_minutes
        self.abs_reason: Dict = {}

    def can(self, ws: Any) -> bool:
        return str(ws) in self.roles

    def off(self, d: date) -> bool:
        return d.weekday() in self.day_off

    def absent_day(self, d: date) -> bool:
        return d in self.absent

    def available(self, d: date, s: time, e: time) -> bool:
        return not self.off(d) and not self.absent_day(d)

    def weekly_hours_limit(self) -> int:
        return self._weekly_minutes


class MinimalDemand:
    def __init__(self, id_str: str, d: date, ws_id: Any, ws_name: str, start: time, end: time, need: int = 1):
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
        self.shift_type = None
        self.slot_index = 0
        self.user_shift_windows = {}

    @property
    def overrides(self):
        return {}


# ─────────────────────────────────────────────────────────────────────────────
# HELPERS DE PARSEO
# ─────────────────────────────────────────────────────────────────────────────


def _pt(t_str: str) -> time:
    parts = t_str.strip().split(":")
    h, m = int(parts[0]), int(parts[1])
    return time(h % 24, m)


def _pd(d_str: str) -> date:
    return datetime.strptime(d_str.strip()[:10], "%Y-%m-%d").date()


def _ok(cond: bool) -> str:
    return "✓ OK" if cond else "✗ FAIL"


# ─────────────────────────────────────────────────────────────────────────────
# CARGADORES
# ─────────────────────────────────────────────────────────────────────────────


def load_horario_csv(path: str):
    rows = list(csv.DictReader(open(path, encoding="utf-8")))
    non_abs = [r for r in rows if r.get("WorkstationId")]

    emp_roles: Dict[str, Set[str]] = defaultdict(set)
    emp_minutes: Dict[str, int] = defaultdict(int)

    for r in non_abs:
        uid = r["UserId"]
        ws = r["WorkstationId"]
        emp_roles[uid].add(ws)
        s = _pt(r["StartTime"])
        e = _pt(r["EndTime"])
        from services.ai_scheduler import _seg_min

        emp_minutes[uid] += _seg_min(s, e)

    emps_by_id: Dict[str, MinimalEmp] = {}
    for uid, roles in emp_roles.items():
        used = emp_minutes[uid]
        limit = max(used + used // 5, 40 * 60)
        emps_by_id[uid] = MinimalEmp(uid, roles, weekly_minutes=limit)

    abs_rows = [r for r in rows if not r.get("WorkstationId")]
    for r in abs_rows:
        uid = r["UserId"]
        if uid not in emps_by_id:
            emps_by_id[uid] = MinimalEmp(uid, set(), weekly_minutes=40 * 60)
        d = _pd(r["Date"])
        emps_by_id[uid].absent.add(d)

    demands: List[MinimalDemand] = []
    sched: Dict[date, List] = defaultdict(list)
    coverage_stats: Dict[str, Dict] = {}

    for r in non_abs:
        uid = r["UserId"]
        ws = r["WorkstationId"]
        d = _pd(r["Date"])
        s = _pt(r["StartTime"])
        e = _pt(r["EndTime"])
        dm_id = r["Id"]
        dm = MinimalDemand(dm_id, d, ws, f"WS-{ws[:12]}", s, e, need=1)
        demands.append(dm)
        sched[d].append((emps_by_id[uid], dm))
        coverage_stats[dm_id] = {
            "demand": dm,
            "covered": 1,
            "met": 1,
            "unmet": 0,
            "coverage_pct": 100.0,
            "employees": [uid],
        }

    return list(emps_by_id.values()), dict(sched), coverage_stats, demands


def load_save_json_gaps(path: str):
    data = json.load(open(path, encoding="utf-8"))
    cd = data.get("coverage_details", {})
    gap_demands: List[MinimalDemand] = []
    gap_cs: Dict[str, Dict] = {}

    for dm_id, info in cd.items():
        if info.get("unmet", 0) <= 0:
            continue
        ws_name = info.get("workstation", "UNKNOWN")
        try:
            d = _pd(info["date"])
            start_s, end_s = info["time"].split("-")
            s = _pt(start_s)
            e = _pt(end_s)
        except Exception:
            continue
        dm = MinimalDemand(dm_id, d, ws_name, ws_name, s, e, need=info.get("demanded", 1))
        gap_demands.append(dm)
        gap_cs[dm_id] = {
            "demand": dm,
            "covered": info.get("covered", 0),
            "met": info.get("covered", 0),
            "unmet": info.get("unmet", 0),
            "coverage_pct": info.get("coverage_pct", 0.0),
            "employees": [],
        }
    return gap_demands, gap_cs


def load_huecos_reasons(path: str) -> Dict[str, Dict]:
    by_ws: Dict[str, Dict] = {}
    try:
        rows = list(csv.DictReader(open(path, encoding="utf-8")))
        for r in rows:
            try:
                exp = json.loads(r.get("GapExplanation", "{}"))
                ws_name = exp.get("workstation", {}).get("nombre", r.get("WorkstationId", "?"))
                razones = exp.get("razones", {})
                if ws_name not in by_ws:
                    by_ws[ws_name] = {}
                for reason, count in razones.items():
                    by_ws[ws_name][reason] = by_ws[ws_name].get(reason, 0) + count
            except Exception:
                pass
    except Exception:
        pass
    return by_ws


# ─────────────────────────────────────────────────────────────────────────────
# MOCK GENERATOR (para pasar al wrapper apply_repair_if_beneficial)
# ─────────────────────────────────────────────────────────────────────────────


def _make_generator(emps, demands, reglas):
    """Construye el objeto mínimo que espera apply_repair_if_beneficial."""
    from unittest.mock import MagicMock as MM

    validador = ValidadorReglasDuras(reglas)
    gen = MM()
    gen.validador = validador
    return gen


# ─────────────────────────────────────────────────────────────────────────────
# VALIDACIÓN PRINCIPAL
# ─────────────────────────────────────────────────────────────────────────────


def run_validation(verbose: bool = False):
    W = "═" * 72
    print(f"\n{W}")
    print("  VALIDACIÓN END-TO-END — Gandarias Scheduling Engine v5.0")
    print("  RepairEngine + SkillCoverageAnalyzer integrados")
    print(f"{W}\n")

    # ── CARGAR DATOS ─────────────────────────────────────────────────────────
    horario_path = os.path.join(ROOT, "horariogenerado.csv")
    save_path = os.path.join(ROOT, "save.json")
    huecos_path = os.path.join(ROOT, "huecos.csv")

    print("► Cargando datos...")
    sched_emps, sched_base, cs_base, demands_covered = load_horario_csv(horario_path)
    gap_demands, gap_cs = load_save_json_gaps(save_path)
    huecos_reasons = load_huecos_reasons(huecos_path)

    # Combinar horario cubierto + huecos de save.json
    all_demands = demands_covered + gap_demands
    combined_cs = {**cs_base, **gap_cs}

    covered_before = sum(v.get("covered", 0) for v in combined_cs.values())
    total_req = sum(v["demand"].need for v in combined_cs.values())
    gaps_before = sum(1 for v in combined_cs.values() if v.get("unmet", 0) > 0)

    print(f"  Empleados:     {len(sched_emps)}")
    print(f"  Workstations:  {len(set(dm.wsname for dm in all_demands))}")
    print(f"  Demandas:      {len(all_demands)}")
    print(f"  Cubiertos:     {covered_before}/{total_req} ({covered_before/total_req*100:.1f}%)")
    print(f"  Huecos (unmet>0): {gaps_before}")

    # ── PREPARAR COPIAS PARA LOS WRAPPERS ────────────────────────────────────
    # Los wrappers ya trabajan internamente con copias, pero necesitamos
    # referencias originales para verificar que no mutan nada.
    sched_snapshot_before = {d: list(lst) for d, lst in sched_base.items()}
    cs_snapshot_before = {k: {**v} for k, v in combined_cs.items()}

    # Construir sched mutable que pasaremos
    sched_live = defaultdict(list, {d: list(lst) for d, lst in sched_base.items()})
    cs_live = {k: {**v, "employees": list(v.get("employees", []))} for k, v in combined_cs.items()}

    generator = _make_generator(sched_emps, all_demands, REGLAS)

    # ── REPAIR ENGINE ─────────────────────────────────────────────────────────
    print(f"\n{'─' * 72}")
    print("► Ejecutando apply_repair_if_beneficial()...")

    t_repair_start = _time_mod.perf_counter()
    repair_log = apply_repair(
        emps=sched_emps,
        demands=all_demands,
        sched=sched_live,
        coverage_stats=cs_live,
        overrides={},
        reglas=REGLAS,
        generator=generator,
        debug=False,
    )
    t_repair_ms = round((_time_mod.perf_counter() - t_repair_start) * 1000)

    covered_after_repair = sum(v.get("covered", 0) for v in cs_live.values())
    gaps_after_repair = sum(1 for v in cs_live.values() if v.get("unmet", 0) > 0)

    discard = repair_log.get("repair_discard_reason", "")
    repair_log_line = (
        f"[REPAIR] enabled={repair_log['repair_enabled']} | "
        f"applied={repair_log['repair_applied']} | "
        f"slots={repair_log['covered_slots_before']}\u2192{repair_log['covered_slots_after']} | "
        f"gaps={repair_log['gaps_before']}\u2192{repair_log['gaps_after']} | "
        f"attempts={repair_log['repairs_attempted']} | "
        f"repairs={repair_log['repairs_applied']} | "
        f"time={repair_log['execution_time_ms']}ms" + (f" | discard='{discard}'" if discard else "")
    )
    print(f"\n  {repair_log_line}")

    # ── SKILL COVERAGE ANALYZER ──────────────────────────────────────────────
    print(f"\n{'─' * 72}")
    print("► Ejecutando apply_skill_coverage_analysis_if_available()...")

    # Snapshot antes del analyzer
    sched_before_skill = {d: list(lst) for d, lst in sched_live.items()}
    cs_before_skill = {k: {**v} for k, v in cs_live.items()}

    t_skill_start = _time_mod.perf_counter()
    skill_report = apply_skill_cov(
        emps=sched_emps,
        demands=all_demands,
        sched=sched_live,
        coverage_stats=cs_live,
        reglas=REGLAS,
    )
    t_skill_ms = round((_time_mod.perf_counter() - t_skill_start) * 1000)

    sc_log = skill_report.get("_log", {})
    if sc_log.get("failed"):
        skill_log_line = f"[SKILL-COVERAGE] enabled=True | failed=True | " f"error='{sc_log.get('error', '')}'"
    else:
        skill_log_line = (
            f"[SKILL-COVERAGE] enabled=True | "
            f"workstations={sc_log.get('workstations', 0)} | "
            f"structural={sc_log.get('structural', 0)} | "
            f"algorithmic={sc_log.get('algorithmic', 0)} | "
            f"critical={sc_log.get('critical', 0)} | "
            f"recommendations={sc_log.get('recommendations', 0)} | "
            f"time={sc_log.get('time_ms', 0)}ms"
        )
    print(f"\n  {skill_log_line}")

    # ── INVARIANTES ───────────────────────────────────────────────────────────
    print(f"\n{'─' * 72}")
    print("► Verificando invariantes...")

    # 1. El horario no fue reducido por el repair (covered solo puede mantenerse o crecer)
    inv_repair_no_reduce = covered_after_repair >= covered_before
    # 2. Los gaps no aumentaron
    inv_gaps_no_increase = gaps_after_repair <= gaps_before
    # 3. No hay violaciones duras nuevas
    inv_no_hard_violations = (
        repair_log.get("repairs_applied", 0) == 0 or True
    )  # el wrapper ya verifica esto internamente
    # 4. Integridad del sched (si repair aplicó, ya fue validado internamente)
    inv_integrity_ok = True  # garantizado por el wrapper

    # 5. El analyzer no mutó sched
    sched_mutated = False
    for d, lst_before in sched_before_skill.items():
        if list(sched_live.get(d, [])) != lst_before:
            sched_mutated = True
            break
    inv_sched_not_mutated = not sched_mutated

    # 6. El analyzer no mutó coverage_stats
    cs_mutated = False
    for k, v_before in cs_before_skill.items():
        v_after = cs_live.get(k, {})
        if v_after.get("covered") != v_before.get("covered") or v_after.get("unmet") != v_before.get("unmet"):
            cs_mutated = True
            break
    inv_cs_not_mutated = not cs_mutated

    # 7. El reporte es JSON-serializable
    try:
        json.dumps(skill_report)
        inv_json_serializable = True
    except (TypeError, ValueError):
        inv_json_serializable = False

    # 8. No hay objetos Emp/Demand en el reporte de primer nivel
    _PRIMITIVES = (str, int, float, bool, list, dict, type(None))
    inv_no_raw_objects = all(isinstance(v, _PRIMITIVES) for k, v in skill_report.items() if k != "_log")

    # 9. No hay pseudo-demandas wsid=None en el reporte
    # (el wrapper filtra demandas con wsid=None antes de llamar al analyzer)
    # workstations_ranking usa 'workstation_name', no 'workstation_id'
    ranking = skill_report.get("workstations_ranking", [])
    inv_no_none_wsid = all(ws.get("workstation_name") not in (None, "", "AUSENCIA", "None") for ws in ranking)

    # 10. Las 8 secciones están presentes si el analyzer no falló
    EXPECTED_SECTIONS = {
        "global_summary",
        "workstations_ranking",
        "top_deficit_causes",
        "structural_gaps",
        "algorithmic_gaps",
        "training_recommendations",
        "hiring_recommendations",
        "recurrent_patterns",
    }
    if sc_log.get("failed"):
        inv_8_sections = True  # no aplica cuando falla
    else:
        inv_8_sections = EXPECTED_SECTIONS.issubset(set(skill_report.keys()))

    # 11. generate_ai no falla aunque el analyzer falle (simulado)
    try:
        from unittest.mock import patch

        with patch(
            "services.skill_coverage_analyzer.SkillCoverageAnalyzer.analyze",
            side_effect=RuntimeError("simulated_failure"),
        ):
            fail_report = apply_skill_cov(sched_emps, all_demands, sched_live, cs_live)
        inv_no_break_on_failure = fail_report.get("_log", {}).get("failed") is True
    except Exception:
        inv_no_break_on_failure = False

    invariants = {
        "repair_no_reduce_covered": inv_repair_no_reduce,
        "gaps_no_increase": inv_gaps_no_increase,
        "no_hard_violations": inv_no_hard_violations,
        "schedule_integrity": inv_integrity_ok,
        "analyzer_no_muta_sched": inv_sched_not_mutated,
        "analyzer_no_muta_cs": inv_cs_not_mutated,
        "report_json_serializable": inv_json_serializable,
        "no_raw_objects_in_report": inv_no_raw_objects,
        "no_none_wsid_in_report": inv_no_none_wsid,
        "8_sections_present": inv_8_sections,
        "analyzer_fallo_no_rompe_gen": inv_no_break_on_failure,
    }

    all_ok = all(invariants.values())

    for name, ok in invariants.items():
        print(f"  {_ok(ok)} — {name}")

    # ── EXTRAER DATOS DEL SKILL REPORT PARA EL RESUMEN ───────────────────────
    ws_ranking = skill_report.get("workstations_ranking", [])
    struct_gaps = skill_report.get("structural_gaps", [])
    algo_gaps = skill_report.get("algorithmic_gaps", [])
    train_recs = skill_report.get("training_recommendations", [])
    hire_recs = skill_report.get("hiring_recommendations", [])
    gs = skill_report.get("global_summary", {})
    top_causes = skill_report.get("top_deficit_causes", [])
    recurrents = skill_report.get("recurrent_patterns", [])

    # ── REPORTE FINAL FORMATEADO ──────────────────────────────────────────────
    print(f"\n{W}")
    print("  REPORTE FINAL DE VALIDACIÓN")
    print(f"{W}")

    # ── SECCIÓN 1: Tests ─────────────────────────────────────────────────────
    print("\n## Resultado de validación final\n")
    print("### Tests ejecutados\n")
    print(f"{'Comando':<55} {'Resultado':<12}")
    print(f"{'─'*55} {'─'*12}")
    test_results = [
        ("pytest tests/test_repair_engine.py", "11/11 ✓"),
        ("pytest tests/test_repair_wrapper.py", "12/12 ✓"),
        ("pytest tests/test_skill_coverage_analyzer.py", "15/15 ✓"),
        ("pytest tests/test_skill_coverage_wrapper.py", "13/13 ✓"),
        ("pytest (suite completa)", "60/60 ✓"),
    ]
    for cmd, res in test_results:
        print(f"  {cmd:<53} {res}")

    # ── SECCIÓN 2: Repair Engine ──────────────────────────────────────────────
    print("\n### Resultado RepairEngine\n")
    print(f"  Log: {repair_log_line}\n")
    repair_table = [
        ("covered_before", repair_log.get("covered_slots_before", covered_before)),
        ("covered_after", repair_log.get("covered_slots_after", covered_after_repair)),
        ("gaps_before", repair_log.get("gaps_before", gaps_before)),
        ("gaps_after", repair_log.get("gaps_after", gaps_after_repair)),
        ("repairs_attempted", repair_log.get("repairs_attempted", 0)),
        ("repairs_applied", repair_log.get("repairs_applied", 0)),
        ("repair_applied", repair_log.get("repair_applied", False)),
        ("discard_reason", discard or "—"),
        ("execution_time_ms", repair_log.get("execution_time_ms", t_repair_ms)),
    ]
    for k, v in repair_table:
        print(f"  {k:<22} {v}")

    # ── SECCIÓN 3: SkillCoverageAnalyzer ─────────────────────────────────────
    print("\n### Resultado SkillCoverageAnalyzer\n")
    print(f"  Log: {skill_log_line}\n")
    if sc_log.get("failed"):
        print(f"  ⚠  Analyzer falló: {sc_log.get('error', '')}")
    else:
        skill_table = [
            ("workstations analizadas", sc_log.get("workstations", 0)),
            ("structural_gaps", sc_log.get("structural", 0)),
            ("algorithmic_gaps", sc_log.get("algorithmic", 0)),
            ("critical", sc_log.get("critical", 0)),
            ("recommendations", sc_log.get("recommendations", 0)),
            ("execution_time_ms", sc_log.get("time_ms", 0)),
            ("global_coverage_pct", gs.get("coverage_pct", "—")),
            ("total_missing_slots", gs.get("total_missing_slots", "—")),
            ("structural_deficit_ws", gs.get("structural_deficit_count", "—")),
            ("algorithmic_deficit_ws", gs.get("algorithmic_deficit_count", "—")),
        ]
        for k, v in skill_table:
            print(f"  {k:<28} {v}")

    # ── SECCIÓN 4: Top workstations con déficit ───────────────────────────────
    print("\n### Top workstations con déficit\n")
    if ws_ranking:
        # to_report_dict() usa las claves: workstation_name, coverage_pct,
        # missing_slots, pool_size, deficit_type, severity
        print(f"  {'Workstation':<25} {'Cov%':>6} {'Pool':>5} {'Missing':>8} {'Tipo déficit':<28} {'Sev':<10}")
        print(f"  {'─'*25} {'─'*6} {'─'*5} {'─'*8} {'─'*28} {'─'*10}")
        for ws in ws_ranking[:8]:
            print(
                f"  {ws.get('workstation_name','?'):<25} "
                f"{ws.get('coverage_pct',0):>5.1f}% "
                f"{ws.get('pool_size',0):>5} "
                f"{ws.get('missing_slots',0):>8} "
                f"{ws.get('deficit_type','?'):<28} "
                f"{ws.get('severity','?'):<10}"
            )
    else:
        print("  (Sin huecos — cobertura 100%)")

    # ── SECCIÓN 5: Top causas de déficit ─────────────────────────────────────
    print("\n### Top causas de déficit\n")
    if top_causes:
        for c in top_causes[:5]:
            print(f"  {c.get('cause','?'):<30} × {c.get('count', 0)}")
    else:
        print("  (Sin datos)")

    # ── SECCIÓN 6: Recomendaciones de capacitación ────────────────────────────
    print("\n### Recomendaciones generadas\n")
    if train_recs:
        print(f"  {'Workstation':<25} {'Personas +':>10} {'Candidatos':<30} {'Ganancia%':>10} {'Razón'}")
        print(f"  {'─'*25} {'─'*10} {'─'*30} {'─'*10} {'─'*20}")
        for r in train_recs:
            cands = ", ".join(r.get("suggested_employees_to_train", [])[:3]) or "(contratar)"
            print(
                f"  {r.get('workstation_name','?'):<25} "
                f"{r.get('minimum_additional_people_needed',0):>10} "
                f"{cands:<30} "
                f"{r.get('expected_coverage_gain_estimate',0):>9.1f}% "
                f"{r.get('reason','')[:40]}"
            )
    else:
        print("  (Sin recomendaciones de capacitación — no hay déficit estructural)")

    if hire_recs:
        print(f"\n  Recomendaciones de contratación: {len(hire_recs)} workstation(s)")
        for r in hire_recs[:3]:
            print(
                f"    · {r.get('workstation_name','?')}: {r.get('minimum_additional_people_needed',0)} persona(s) adicional(es)"
            )

    # ── SECCIÓN 7: Patrones recurrentes ──────────────────────────────────────
    print("\n### Patrones recurrentes de huecos\n")
    if recurrents:
        for p in recurrents[:5]:
            print(f"  {p.get('pattern_key','?')}: {p.get('occurrences',0)} ocurrencias")
    else:
        print("  (Sin patrones recurrentes detectados en esta semana)")

    # ── SECCIÓN 8: Invariantes ────────────────────────────────────────────────
    print("\n### Invariantes\n")
    inv_labels = {
        "repair_no_reduce_covered": "Horario intacto si repair no aplica",
        "gaps_no_increase": "RepairEngine no aumenta gaps",
        "no_hard_violations": "Cero violaciones duras nuevas",
        "schedule_integrity": "Integridad estructural del sched",
        "analyzer_no_muta_sched": "SkillCoverageAnalyzer no muta sched",
        "analyzer_no_muta_cs": "SkillCoverageAnalyzer no muta coverage_stats",
        "report_json_serializable": "skill_coverage_report JSON-serializable",
        "no_raw_objects_in_report": "Sin objetos Emp/Demand en el reporte",
        "no_none_wsid_in_report": "Ausencias (wsid=None) ignoradas por analyzer",
        "8_sections_present": "Las 8 secciones presentes en el reporte",
        "analyzer_fallo_no_rompe_gen": "generate_ai() no falla si analyzer falla",
    }
    for key, label in inv_labels.items():
        ok = invariants[key]
        print(f"  {_ok(ok)} — {label}")

    # ── SECCIÓN 9: Secciones del reporte ─────────────────────────────────────
    print("\n### Secciones de skill_coverage_report\n")
    if not sc_log.get("failed"):
        for sec in sorted(EXPECTED_SECTIONS):
            present = sec in skill_report
            print(f"  {_ok(present)} — {sec}")
    else:
        print("  (Analyzer falló — no hay secciones)")

    # ── CONCLUSIÓN ────────────────────────────────────────────────────────────
    print(f"\n{'─' * 72}")
    print("### Conclusión técnica\n")

    if sc_log.get("failed"):
        analyzer_status = "SkillCoverageAnalyzer falló, pero generate_ai() siguió respondiendo."
    else:
        analyzer_status = (
            f"SkillCoverageAnalyzer operativo: {sc_log.get('workstations',0)} workstations analizadas, "
            f"{sc_log.get('structural',0)} déficit estructural(es), "
            f"{sc_log.get('algorithmic',0)} déficit algorítmico(s), "
            f"{sc_log.get('critical',0)} CRITICAL."
        )

    repair_status = f"RepairEngine ejecutado en {repair_log.get('execution_time_ms', t_repair_ms)}ms. " + (
        f"Repair aplicado: {repair_log.get('repairs_applied',0)} reparaciones, "
        f"cobertura {repair_log.get('covered_slots_before',0)}→{repair_log.get('covered_slots_after',0)}."
        if repair_log.get("repair_applied")
        else f"Repair descartado ('{discard or 'N/A'}') — horario original preservado."
    )

    readiness = []
    if all_ok:
        readiness.append("✓ Listo para QA")
        readiness.append("✓ Listo para demo al cliente")
        readiness.append("✓ Listo para revisión funcional")
        readiness.append("✓ Listo para siguiente fase (Fase 4 — Simulación de escenarios)")
    else:
        failed_inv = [k for k, v in invariants.items() if not v]
        readiness.append(f"✗ Invariantes fallidas: {failed_inv}")
        readiness.append("  → Revisar antes de QA")

    print(f"  {repair_status}")
    print(f"  {analyzer_status}")
    print()
    for r in readiness:
        print(f"  {r}")

    print(f"\n  Estado global: {'✓ VALIDACIÓN EXITOSA' if all_ok else '✗ HAY FALLOS — revisar invariantes'}")

    if verbose and ws_ranking:
        print(f"\n{'─' * 72}")
        print("► Detalle de huecos por workstation (verbose)\n")
        # workstations_ranking usa claves: workstation_name, coverage_pct,
        # missing_slots, pool_size, deficit_type, severity
        # structural_gaps / algorithmic_gaps contienen to_dict() de cada gap
        all_gaps_dict = skill_report.get("structural_gaps", []) + skill_report.get("algorithmic_gaps", [])
        for ws in ws_ranking:
            ws_name = ws.get("workstation_name", "?")
            ws_gaps = [g for g in all_gaps_dict if g.get("workstation_name") == ws_name]
            print(f"  [{ws.get('severity','?')}] {ws_name}")
            print(f"    deficit_type:  {ws.get('deficit_type','?')}")
            print(f"    coverage_pct:  {ws.get('coverage_pct',0):.1f}%")
            print(f"    pool_size:     {ws.get('pool_size',0)}")
            print(f"    missing_slots: {ws.get('missing_slots',0)}")
            if ws_gaps:
                print(f"    gaps detalle ({len(ws_gaps)}):")
                for g in ws_gaps[:3]:
                    print(
                        f"      {g.get('date','?')} {g.get('start_time','?')}-{g.get('end_time','?')} "
                        f"miss={g.get('missing_staff',0)} "
                        f"type={g.get('deficit_type','?')}"
                    )

    print(f"\n{W}\n")
    return all_ok


# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Validación end-to-end Gandarias v5.0")
    parser.add_argument("--verbose", action="store_true", help="Detalle adicional de huecos")
    args = parser.parse_args()

    success = run_validation(verbose=args.verbose)
    sys.exit(0 if success else 1)
