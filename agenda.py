#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGENDA GENERATOR API – Gandarías v4.2 (IA + reglas + feedback loop)
==================================================================
CORRECCIONES v4.1:
  - Query empleados: ComplementHours (no IsSplitShift), IsActive AND NOT IsDelete
  - UserShift enforcement: plan_usershift_day_modes() → overrides para AI generator
  - Hybrid 0.5 postprocess: apply_hybrid_05_postprocess() portado del viejo
  - Min 3h validado POR BLOQUE individual (no total/día)
  - Gap split 3h entre bloques del mismo día validado
"""
import logging
import os
import uuid
from collections import defaultdict
from datetime import date, datetime, time, timedelta, timezone
from typing import Dict, Tuple, List, Set, Any

import psycopg2
from flask import Flask, jsonify, request
from flask_cors import CORS
from psycopg2 import DataError, OperationalError, ProgrammingError

from services.ai_scheduler import (
    AIScheduleGenerator, ExtractorPatrones, ModeloPatrones,
    _t2m, _m2t, _end_eff, _seg_min, _merge_intervals, _has_overlap, _uid,
    REGLAS_DURAS_DEFAULTS,
)

# ───────── CONFIG ─────────
ASCII_LOGS = True
MIN_HOURS_BETWEEN_SHIFTS = 9
MIN_HOURS_BETWEEN_SPLIT = 3
MIN_SEGMENT_MINUTES = 15
MAX_HOURS_PER_DAY = 9
MIN_SHIFT_DURATION_HOURS = 3
MAX_DAYS_PER_WEEK = 6

CSV_ENTRENAMIENTO = os.environ.get(
    "CSV_ENTRENAMIENTO",
    os.path.join(os.path.dirname(__file__), "_Schedules__202601300806.csv"),
)

ROLE_FALLBACKS_BY_NAME = {
    "JEFE BARRA": ["ENLACE", "APOYO ENLACE", "CAMARERO BARRA"],
    "ENLACE": ["APOYO ENLACE"],
    "JEFE COMEDOR": ["CAMARERO COMEDOR"],
    "CAMARERO BARRA": ["APERTURA BARRA"],
}

app = Flask(__name__)
CORS(app)

DB = {
    "host": "database-gandarias.ct6gmyi80fdr.eu-central-1.rds.amazonaws.com",
    "port": 5432, "dbname": "postgresqa",
    "user": "postgres", "password": "MyStrongPassword!123_",
}

def uid(): return str(uuid.uuid4())
def now(): return datetime.now(timezone.utc)

class DatabaseConnectionError(Exception): ...
class DataNotFoundError(Exception): ...
class DataIntegrityError(Exception): ...
class ScheduleGenerationError(Exception): ...


# ═══════════════════════════════════════════════════════════════════
# MODELS
# ═══════════════════════════════════════════════════════════════════

class Emp:
    def __init__(self, row: Tuple):
        self.id, self.name, self.split = row
        self.roles: Set = set()
        self.day_off: Set[int] = set()
        self.window = defaultdict(list)
        self.exc = defaultdict(list)
        self.absent: Set[date] = set()
        self.abs_reason: Dict[date, str] = {}
        self.user_shifts = defaultdict(set)
        self.user_shift_windows = defaultdict(list)
        self.shift_type_restrictions = set()
        self.shift_type_restr_by_dow = defaultdict(set)
        self.shift_type_windows = defaultdict(list)
        self.us_two_starts_dow: Set[int] = set()
        self.user_shift_anchor_by_date = {}

    def can(self, ws): return ws in self.roles
    def off(self, d: date) -> bool: return d.weekday() in self.day_off
    def absent_day(self, d: date) -> bool: return d in self.absent

    def available(self, d: date, s: time, e: time) -> bool:
        if self.off(d) or self.absent_day(d): return False
        if not self.day_off and not self.window and not self.exc: return True
        win = self.exc.get(d) or self.window.get(d.weekday())
        if not win: return False
        end = e if e != time(0, 0) else time(23, 59)
        for a, b in win:
            b2 = b if b != time(0, 0) else time(23, 59)
            if s >= a and end <= b2: return True
        return False


class Demand:
    def __init__(self, row: Tuple):
        (self.id, rdate, self.wsid, self.wsname, self.start, self.end, need) = row
        self.date = rdate.date() if hasattr(rdate, 'date') else rdate
        try:
            self.raw_need = float(need) if need is not None else 0.0
        except (TypeError, ValueError):
            self.raw_need = 0.0
        self.is_hybrid_05 = abs(self.raw_need - 0.5) < 1e-6
        self.need = 1 if self.is_hybrid_05 else (int(round(self.raw_need)) if self.raw_need > 0 else 0)
        self.slot_index = 0
        self.shift_type = None

    def __repr__(self):
        return (f"Demand(id={self.id}, date={self.date}, ws={self.wsname}, "
                f"{self.start}-{self.end}, need={self.need}, hyb={self.is_hybrid_05})")


# ═══════════════════════════════════════════════════════════════════
# BD HELPERS
# ═══════════════════════════════════════════════════════════════════

def conn():
    try:
        return psycopg2.connect(**DB)
    except OperationalError as e:
        t = str(e)
        if "could not connect" in t: raise DatabaseConnectionError("No se puede conectar a BD")
        if "authentication failed" in t: raise DatabaseConnectionError("Credenciales BD incorrectas")
        raise DatabaseConnectionError(t)

def fetchall(cur, sql, pars=None):
    try:
        cur.execute(sql, pars) if pars else cur.execute(sql)
        return cur.fetchall()
    except (ProgrammingError, DataError) as e:
        raise DataIntegrityError(str(e))

def monday(d: date) -> date:
    return d - timedelta(days=d.weekday())

def duration_min(dm) -> int:
    return _seg_min(dm.start, dm.end)


# ═══════════════════════════════════════════════════════════════════
# DEMAND PROCESSING
# ═══════════════════════════════════════════════════════════════════

def split_long_segment(d, wsid, wsname, s_min, e_min, need, max_hours, raw_need=None):
    out, limit, cur = [], max_hours * 60, s_min
    eff = need if raw_need is None else raw_need
    while cur < e_min:
        nxt = min(cur + limit, e_min)
        out.append(Demand((uid(), d, wsid, wsname, _m2t(cur),
                           _m2t(nxt if nxt < 1440 else 0), eff)))
        cur = nxt
    return out

def coalesce_demands(demands, tolerate_gap_min=0):
    by_key = defaultdict(list)
    for d in demands: by_key[(d.date, d.wsid, d.wsname)].append(d)
    merged = []
    for (dte, wsid, wsname), items in by_key.items():
        items.sort(key=lambda x: (_t2m(x.start), _t2m(x.end)))
        if not items: continue
        curr = items[0]
        for nxt in items[1:]:
            c_end, n_start = _t2m(_end_eff(curr.end)), _t2m(nxt.start)
            if n_start <= c_end + tolerate_gap_min and nxt.need == curr.need:
                curr = Demand((curr.id, dte, wsid, wsname, curr.start, nxt.end, curr.raw_need))
            else:
                merged.append(curr); curr = nxt
        merged.append(curr)
    return merged

def normalize_by_max_need_profile(demands):
    result = []
    for dm in demands:
        dur_min = _seg_min(dm.start, dm.end)
        if dur_min > MAX_HOURS_PER_DAY * 60 and dm.need > 0:
            result.extend(split_long_segment(
                dm.date, dm.wsid, dm.wsname,
                _t2m(dm.start), _t2m(_end_eff(dm.end)),
                dm.need, MAX_HOURS_PER_DAY, dm.raw_need))
        else:
            result.append(dm)
    return result


# ═══════════════════════════════════════════════════════════════════
# LAW RESTRICTIONS
# ═══════════════════════════════════════════════════════════════════

LAW_IDS = {
    "max_hours_per_day":        "feedc36b-debf-4f51-b882-194c3816c4d1",
    "min_hours_between_split":  "1b52f06b-64d9-40a0-bcf5-c922cfc937c2",
    "min_shift_duration_hours": "df056d24-7d3a-416a-949f-3f0b491515e4",
    "min_hours_between_shifts": "be491f3f-059b-42ed-adc4-331754d85412",
    "min_days_off_per_week":    "756d9660-5101-4673-892b-267b38dc805e",
}

def fetch_law_restrictions_by_id(ids=None):
    ids = ids or LAW_IDS
    id_list = list(ids.values())
    resolved = {k: None for k in ids}
    with conn() as c, c.cursor() as cur:
        rows = fetchall(cur, '''
            SELECT "Id"::text, "Description", "CantHours"
            FROM "Management"."LawRestrictions"
            WHERE "Id" = ANY(%s::uuid[])
        ''', (id_list,))
    by_id = {r[0]: {"description": r[1], "hours": int(r[2]) if r[2] is not None else None} for r in rows}
    for k, u in ids.items():
        info = by_id.get(u)
        if info: resolved[k] = info["hours"]
    return {"resolved": resolved}


# ═══════════════════════════════════════════════════════════════════
# TEMPLATE
# ═══════════════════════════════════════════════════════════════════

def pick_template(cur, week_start, week_end):
    act = fetchall(cur, '''SELECT "Id","Name" FROM "Management"."WorkstationDemandTemplates" WHERE "IsActive" = TRUE''')
    if len(act) == 1: return act[0]
    if len(act) > 1: raise DataIntegrityError("Hay varias plantillas activas")
    rows = fetchall(cur, '''
        SELECT "Id","Name","StartDate"::date,"EndDate"::date,
               COALESCE("DateCreated", '-infinity'::timestamptz) AS created,
               (SELECT COUNT(*) FROM "Management"."WorkstationDemands" d WHERE d."TemplateId" = t."Id") AS demandas
        FROM "Management"."WorkstationDemandTemplates" t
        WHERE "StartDate" IS NOT NULL AND "EndDate" IS NOT NULL
        ORDER BY "StartDate","EndDate","Id"
    ''')
    if not rows: raise DataNotFoundError("No existen plantillas con demandas")
    chosen = next((r for r in rows if int(r[5] or 0) > 0), None)
    if chosen: return (chosen[0], chosen[1])
    raise DataNotFoundError("No hay plantilla con demandas > 0")


# ═══════════════════════════════════════════════════════════════════
# USERSHIFT DAY MODES (portado del viejo agenda.py)
# ═══════════════════════════════════════════════════════════════════

def _usershift_day_eligibility(emp, ddate):
    """
    Evalúa si un empleado tiene UserShift válido para ese día.
    Returns: (ok, kind, reason)
    """
    dow = ddate.weekday()
    wins = sorted(emp.user_shift_windows.get(dow, []),
                  key=lambda w: (_t2m(w[0]), _t2m(w[1])))
    if not wins:
        return False, None, "no_usershift_for_day"
    # Merge solapados
    merged = []
    for s, e in wins:
        smin = _t2m(s)
        emin = _t2m(e if e != time(0, 0) else time(23, 59))
        if not merged or smin > merged[-1][1]:
            merged.append([smin, emin])
        else:
            merged[-1][1] = max(merged[-1][1], emin)
    if len(merged) == 1:
        return True, "single", "ok"
    if len(merged) >= 2:
        gap = merged[1][0] - merged[0][1]
        if gap >= MIN_HOURS_BETWEEN_SPLIT * 60:
            return True, "split", "ok"
        return False, None, "usershift_split_gap_lt_min"
    return False, None, "unsupported"


def _minutes_candidate_in_usershift(emp, ddate, demands):
    """Minutos de demanda dentro de ventanas UserShift del día."""
    dow = ddate.weekday()
    wins = emp.user_shift_windows.get(dow)
    if not wins: return 0, "no_usershift_for_day"
    total = 0; any_inside = False
    for dm in demands:
        if dm.date != ddate: continue
        if not emp.can(dm.wsid): continue
        end = dm.end if dm.end != time(0, 0) else time(23, 59)
        for w_s, w_e in wins:
            w_end = w_e if w_e != time(0, 0) else time(23, 59)
            if dm.start >= w_s and end <= w_end:
                any_inside = True
                total += duration_min(dm)
                break
    if not any_inside: return 0, "no_demands_inside_window"
    if total < MIN_SHIFT_DURATION_HOURS * 60: return total, "insufficient_volume_for_3h"
    return total, "ok"


def plan_usershift_day_modes(emps, demands, week):
    """
    Determina para cada (emp, día) si UserShift se enfuerza o es libre.
    Returns: overrides set, plan dict
    overrides = {(emp_id_str, date)} → días donde el empleado queda en modo libre
    """
    overrides = set()
    plan = {}
    by_date = defaultdict(list)
    for dm in demands: by_date[dm.date].append(dm)

    for emp in emps:
        for d in week:
            ok, kind, reason = _usershift_day_eligibility(emp, d)
            if not ok:
                plan[(str(emp.id), d)] = {"mode": "free", "reason": reason}
                overrides.add((str(emp.id), d))
                continue
            total_min, why = _minutes_candidate_in_usershift(emp, d, by_date.get(d, []))
            if total_min >= MIN_SHIFT_DURATION_HOURS * 60:
                plan[(str(emp.id), d)] = {"mode": "enforced", "reason": "ok", "kind": kind}
            else:
                plan[(str(emp.id), d)] = {"mode": "free", "reason": why}
                overrides.add((str(emp.id), d))

    if ASCII_LOGS:
        enforced = sum(1 for v in plan.values() if v["mode"] == "enforced")
        free = sum(1 for v in plan.values() if v["mode"] == "free")
        print(f"[USERSHIFT] {enforced} enforced, {free} free, {len(overrides)} overrides")

    return overrides, plan


# ═══════════════════════════════════════════════════════════════════
# HYBRID 0.5 POSTPROCESS (portado del viejo agenda.py)
# ═══════════════════════════════════════════════════════════════════

def apply_hybrid_05_postprocess(emps, demands, week, sched, coverage_stats, overrides):
    """
    Post-proceso para puestos híbridos (EffortRequired = 0.5).
    Un empleado cubre 2 workstations distintos en el mismo bloque horario.
    """
    hybrid_demand_ids = set()
    for dm in demands:
        if getattr(dm, "is_hybrid_05", False):
            hybrid_demand_ids.add(dm.id)

    if not hybrid_demand_ids:
        return

    # Limpiar asignaciones híbridas previas
    for day in list(sched.keys()):
        sched[day] = [(emp, dm) for (emp, dm) in sched[day]
                      if dm.id not in hybrid_demand_ids]

    for dm_id in hybrid_demand_ids:
        if dm_id in coverage_stats:
            coverage_stats[dm_id]["met"] = 0
            coverage_stats[dm_id]["covered"] = 0
            coverage_stats[dm_id]["unmet"] = coverage_stats[dm_id]["demand"].need

    # Agrupar híbridos por (día, workstation)
    demands_by_day_ws = defaultdict(list)
    for dm in demands:
        if not getattr(dm, "is_hybrid_05", False): continue
        demands_by_day_ws[(dm.date, dm.wsname)].append(dm)
    for k in demands_by_day_ws:
        demands_by_day_ws[k].sort(key=lambda d: _t2m(d.start))

    days_with_hybrids = set(dm.date for dm in demands if getattr(dm, "is_hybrid_05", False))
    MIN_BLK = MIN_SHIFT_DURATION_HOURS * 60
    MAX_BLK = MAX_HOURS_PER_DAY * 60

    for day in sorted(days_with_hybrids):
        workstations = set()
        for (d, ws), dms in demands_by_day_ws.items():
            if d == day: workstations.add(ws)
        if len(workstations) < 2: continue

        # Intentar parear workstations
        ws_list = sorted(workstations)
        from itertools import combinations
        for ws_a, ws_b in combinations(ws_list, 2):
            dms_a = demands_by_day_ws.get((day, ws_a), [])
            dms_b = demands_by_day_ws.get((day, ws_b), [])
            if not dms_a or not dms_b: continue

            # Calcular rango total
            all_start = min(_t2m(d.start) for d in dms_a + dms_b)
            all_end = max(_t2m(_end_eff(d.end)) for d in dms_a + dms_b)
            total_dur = all_end - all_start
            if total_dur < MIN_BLK or total_dur > MAX_BLK: continue

            # Buscar empleado que pueda ambos puestos
            wsid_a = dms_a[0].wsid
            wsid_b = dms_b[0].wsid
            for emp in emps:
                if not emp.can(wsid_a) or not emp.can(wsid_b): continue
                if emp.off(day) or emp.absent_day(day): continue
                if not emp.available(day, _m2t(all_start), _m2t(all_end)): continue

                # Verificar que no esté ya asignado a esas horas
                existing = [(e, dm) for e, dm in sched.get(day, []) if str(e.id) == str(emp.id)]
                existing_ivs = [(_t2m(dm.start), _t2m(_end_eff(dm.end)))
                                for _, dm in existing if dm.wsid]
                if _has_overlap(existing_ivs, all_start, all_end): continue

                # Asignar mitad a cada ws
                for dm_a in dms_a:
                    if coverage_stats.get(dm_a.id, {}).get("unmet", 0) > 0:
                        sched[day].append((emp, dm_a))
                        coverage_stats[dm_a.id]["covered"] += 1
                        coverage_stats[dm_a.id]["met"] += 1
                        coverage_stats[dm_a.id]["unmet"] = max(0, coverage_stats[dm_a.id]["unmet"] - 1)
                for dm_b in dms_b:
                    if coverage_stats.get(dm_b.id, {}).get("unmet", 0) > 0:
                        sched[day].append((emp, dm_b))
                        coverage_stats[dm_b.id]["covered"] += 1
                        coverage_stats[dm_b.id]["met"] += 1
                        coverage_stats[dm_b.id]["unmet"] = max(0, coverage_stats[dm_b.id]["unmet"] - 1)
                break  # Un empleado por par


# ═══════════════════════════════════════════════════════════════════
# LOAD DATA (CORREGIDO: ComplementHours, IsActive AND NOT IsDelete)
# ═══════════════════════════════════════════════════════════════════

def load_data(week_start: date):
    week = [week_start + timedelta(days=i) for i in range(7)]
    week_end = week[-1]

    def _to_time(x):
        if x is None: return None
        if isinstance(x, time): return x
        if isinstance(x, timedelta): return (datetime.min + x).time()
        try: return (datetime.min + x).time()
        except: return None

    def _pair(s, e):
        s, e = _to_time(s), _to_time(e)
        if not s or not e: return None
        e = e if e != time(0, 0) else time(23, 59)
        return (s, e) if s < e else None

    def _complement_blocks(blocks):
        DAY_START, DAY_END = time(0, 0), time(23, 59)
        ivs = sorted([p for p in blocks if p], key=lambda p: (p[0], p[1]))
        merged = []
        for s, e in ivs:
            if not merged: merged.append([s, e])
            else:
                if s <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], e)
                else: merged.append([s, e])
        out, cur_t = [], DAY_START
        for s, e in merged:
            if cur_t < s: out.append((cur_t, s))
            cur_t = max(cur_t, e)
        if cur_t < DAY_END: out.append((cur_t, DAY_END))
        return out

    with conn() as c, c.cursor() as cur:
        # Laws
        global MIN_HOURS_BETWEEN_SPLIT, MIN_HOURS_BETWEEN_SHIFTS
        global MAX_HOURS_PER_DAY, MIN_SHIFT_DURATION_HOURS

        laws = fetch_law_restrictions_by_id()
        L = laws["resolved"] if laws else {}
        MAX_HOURS_PER_DAY = int(L.get("max_hours_per_day") or 9)
        MIN_HOURS_BETWEEN_SPLIT = int(L.get("min_hours_between_split") or 3)
        MIN_SHIFT_DURATION_HOURS = int(L.get("min_shift_duration_hours") or 3)
        MIN_HOURS_BETWEEN_SHIFTS = int(L.get("min_hours_between_shifts") or 9)
        MIN_DAYS_OFF = int(L.get("min_days_off_per_week") or 2)

        if ASCII_LOGS:
            print(f"[LAW] MAX_H={MAX_HOURS_PER_DAY}h MIN_SHIFT={MIN_SHIFT_DURATION_HOURS}h "
                  f"MIN_SPLIT={MIN_HOURS_BETWEEN_SPLIT}h MIN_REST={MIN_HOURS_BETWEEN_SHIFTS}h "
                  f"MIN_OFF={MIN_DAYS_OFF}")

        # Template
        tpl_id, tpl_name = pick_template(cur, week_start, week_end)
        print(f"[DATA] Template: {tpl_name} ({tpl_id})")

        # Demands
        demands = [
            Demand(r) for r in fetchall(cur, '''
                SELECT d."Id", %s + d."Day"*interval '1 day',
                       d."WorkstationId", w."Name",
                       (TIMESTAMP '2000-01-01'+d."StartTime")::time,
                       (TIMESTAMP '2000-01-01'+d."EndTime")::time,
                       d."EffortRequired"
                FROM "Management"."WorkstationDemands" d
                JOIN "Management"."Workstations" w ON w."Id" = d."WorkstationId"
                WHERE d."TemplateId" = %s
                ORDER BY d."Day", d."StartTime", d."EndTime", d."Id"
            ''', (week_start, tpl_id))
        ]
        demands = coalesce_demands(demands, tolerate_gap_min=0)
        demands = normalize_by_max_need_profile(demands)
        print(f"[DATA] {len(demands)} demands")

        # ── EMPLEADOS (CORREGIDO: ComplementHours, no IsSplitShift) ──
        emps_map = {
            r[0]: Emp(r) for r in fetchall(cur, '''
                SELECT "Id",
                       COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                       COALESCE("ComplementHours", TRUE)
                FROM "Management"."AspNetUsers"
                WHERE "IsActive" AND NOT "IsDelete"
                ORDER BY "LastName","FirstName","Id"
            ''')
        }
        if not emps_map: raise DataNotFoundError("No hay empleados activos")

        # Roles
        for uid2, ws in fetchall(cur, '''
            SELECT "UserId","WorkstationId" FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete" ORDER BY "UserId","WorkstationId"
        '''):
            if uid2 in emps_map: emps_map[uid2].roles.add(ws)

        emps = [emps_map[k] for k in sorted(emps_map.keys())]

        # Role fallbacks
        name2id = {}
        for _dm in demands: name2id[_dm.wsname.upper()] = _dm.wsid
        for _e in emps:
            _e.roles_originales = set(_e.roles)
            for _r in list(_e.roles):
                for _t in ROLE_FALLBACKS_BY_NAME.get(
                    next((n for n, i in name2id.items() if i == _r), ""), []):
                    tid = name2id.get(_t.upper())
                    if tid: _e.roles.add(tid)

        # Ausentismos
        for uid_abs, sd, ed in fetchall(cur, '''
            SELECT "UserId", "StartDate"::date, COALESCE("EndDate"::date, %s)
            FROM "Management"."UserAbsenteeisms"
            WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date, %s) >= %s
            ORDER BY "UserId","StartDate","EndDate"
        ''', (week_end, week_end, week_end, week_start)):
            if uid_abs not in emps_map: continue
            emp = emps_map[uid_abs]
            d0 = max(sd, week_start)
            while d0 <= ed:
                emp.absent.add(d0); emp.abs_reason[d0] = 'ABS'; emp.exc[d0] = []
                d0 += timedelta(days=1)

        # Restricciones semanales
        for uid3, dow, rt, f1, t1, b1s, b1e, b2s, b2e in fetchall(cur, '''
            SELECT "UserId","DayOfWeek","RestrictionType",
                   "AvailableFrom","AvailableUntil",
                   "Block1Start","Block1End","Block2Start","Block2End"
            FROM "Management"."EmployeeScheduleRestrictions"
            ORDER BY "UserId","DayOfWeek","RestrictionType"
        '''):
            if uid3 not in emps_map: continue
            emp = emps_map[uid3]
            if rt == 0: emp.day_off.add(dow); continue
            if rt == 1: emp.window[dow].append((time(0, 0), time(23, 59))); continue
            if rt == 2:
                s = _to_time(f1); e = _to_time(t1)
                if s is None and e is None: continue
                if s is not None and e is None: e = time(23, 59)
                if s is None: s = time(0, 0)
                if e == time(0, 0): e = time(23, 59)
                if s < e: emp.window[dow].append((s, e))
                continue
            if rt == 3:
                t = _to_time(t1)
                if t: emp.window[dow].append((time(0, 0), t if t != time(0, 0) else time(23, 59)))
                continue
            if rt == 4:
                p1 = _pair(b1s, b1e); p2 = _pair(b2s, b2e)
                if p1: emp.window[dow].append(p1)
                if p2: emp.window[dow].append(p2)
                if not p1 and not p2:
                    p = _pair(f1, t1)
                    if p: emp.window[dow].append(p)
                continue
            if rt == 5:
                blocked = []
                p1 = _pair(b1s, b1e); p2 = _pair(b2s, b2e)
                if p1: blocked.append(p1)
                if p2: blocked.append(p2)
                if not blocked:
                    p = _pair(f1, t1)
                    if p: blocked.append(p)
                for w in _complement_blocks(blocked): emp.window[dow].append(w)

        # Excepciones
        for uid4, d_exc, rt, f, t in fetchall(cur, '''
            SELECT "UserId","Date","RestrictionType","AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s ORDER BY "UserId","Date","RestrictionType"
        ''', (week_start, week_end)):
            if uid4 not in emps_map: continue
            emp = emps_map[uid4]
            if rt == 0:
                emp.absent.add(d_exc)
                emp.abs_reason[d_exc] = emp.abs_reason.get(d_exc, 'VAC')
            else:
                s = _to_time(f); e = _to_time(t)
                if s and e and s < e:
                    if e == time(0, 0): e = time(23, 59)
                    emp.exc[d_exc].append((s, e))

        # Licencias
        for uid5, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
            FROM "Management"."Licenses"
            WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
            ORDER BY "UserId","StartDate","EndDate"
        ''', (week_end, week_end, week_end, week_start)):
            if uid5 not in emps_map: continue
            emp = emps_map[uid5]
            d0 = max(sd, week_start)
            while d0 <= ed:
                emp.absent.add(d0); emp.abs_reason[d0] = 'VAC'
                d0 += timedelta(days=1)

        # ShiftTypes
        shift_types = []
        for row in fetchall(cur, '''
            SELECT "Id","Name","Description",
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time,
                   "Structure" = 1,
                   (TIMESTAMP '2000-01-01' + COALESCE("Block2Start", INTERVAL '00:00:00'))::time,
                   (TIMESTAMP '2000-01-01' + COALESCE("Block2lastStart", INTERVAL '00:00:00'))::time,
                   "IsActive"
            FROM "Management"."ShiftTypes" WHERE "IsActive" = TRUE ORDER BY "Name","Id"
        '''):
            shift_types.append({
                'id': row[0], 'name': row[1], 'description': row[2],
                'start_time': row[3], 'end_time': row[4], 'is_split': row[5],
                'b2_start': row[6], 'b2_end': row[7], 'is_active': row[8],
            })
        shift_types_by_id = {st['id']: st for st in shift_types}

        # ShiftType restrictions
        for uidX, dowX, stid in fetchall(cur, '''
            SELECT "UserId","DayOfWeek","ShiftTypeId"
            FROM "Management"."EmployeeShiftTypeRestrictions"
            ORDER BY "UserId","DayOfWeek","ShiftTypeId"
        '''):
            if uidX not in emps_map or stid not in shift_types_by_id: continue
            emp = emps_map[uidX]; st = shift_types_by_id[stid]
            emp.shift_type_restr_by_dow[dowX].add(stid)
            _cap = lambda t: t if t != time(0, 0) else time(23, 59)
            if st['start_time'] and st['end_time'] and st['start_time'] < _cap(st['end_time']):
                emp.shift_type_windows[dowX].append((st['start_time'], _cap(st['end_time'])))
            if st['is_split'] and st.get('b2_start') and st.get('b2_end') and st['b2_start'] < _cap(st['b2_end']):
                emp.shift_type_windows[dowX].append((st['b2_start'], _cap(st['b2_end'])))

        # UserShifts → construir ventanas directamente de Block1/Block2
        def _cap_end_from_start(start_t, candidate_end):
            end_eff = candidate_end or time(23, 59)
            if end_eff == time(0, 0): end_eff = time(23, 59)
            end_m = min(_t2m(end_eff), _t2m(start_t) + MAX_HOURS_PER_DAY * 60)
            return _m2t(end_m if end_m < 24 * 60 else 0)

        def _plus_minutes(t, minutes):
            return _m2t(min(_t2m(t) + minutes, 24 * 60 - 1))

        MIN_BLOCK_MIN = MIN_SHIFT_DURATION_HOURS * 60
        GAP_MIN = MIN_HOURS_BETWEEN_SPLIT * 60
        DAY_MAX_MIN = MAX_HOURS_PER_DAY * 60

        us_rows = fetchall(cur, '''
            SELECT "UserId","Day","Structure",
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time,
                   (TIMESTAMP '2000-01-01' + "Block2Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block2lastStart")::time
            FROM "Management"."UserShifts"
            ORDER BY "UserId","Day","Block1Start","Block2Start"
        ''')

        us_groups = defaultdict(list)
        for uid7, day7, structure7, b1s, b1e, b2s, b2e in us_rows:
            us_groups[(uid7, day7)].append((structure7, b1s, b1e, b2s, b2e))

        for e in emps:
            e.has_us_row_by_dow = defaultdict(bool)
            e.no_assign_by_date = set()

        for (uid7, day7), rows7 in us_groups.items():
            if uid7 not in emps_map: continue
            emp = emps_map[uid7]
            emp.has_us_row_by_dow[day7] = True
            windows = []

            b1_starts = [r[1] for r in rows7 if r[1] is not None]
            b1_ends   = [r[2] for r in rows7 if r[2] is not None]
            b2_any    = any(r[3] is not None or r[4] is not None for r in rows7)
            multi_b1_no_end = (len(b1_starts) >= 2) and (len(b1_ends) == 0) and (not b2_any)

            if multi_b1_no_end:
                starts_sorted = sorted(b1_starts, key=_t2m)[:2]
                s1, s2 = starts_sorted[0], starts_sorted[1]
                if _t2m(s2) - _t2m(s1) < GAP_MIN:
                    end_cont = _cap_end_from_start(s1, _plus_minutes(s1, DAY_MAX_MIN))
                    if _t2m(end_cont) - _t2m(s1) < MIN_BLOCK_MIN:
                        end_cont = _plus_minutes(s1, MIN_BLOCK_MIN)
                    windows.append((s1, end_cont))
                else:
                    e1 = _plus_minutes(s1, MIN_BLOCK_MIN)
                    windows.append((s1, e1))
                    start2 = max(s2, _plus_minutes(e1, GAP_MIN))
                    late_allow_min = max(0, DAY_MAX_MIN - MIN_BLOCK_MIN)
                    e2 = _m2t(min(_t2m(start2) + late_allow_min, 24 * 60 - 1))
                    if start2 < e2:
                        windows.append((start2, e2))
                for ws7, we7 in windows:
                    if ws7 < we7:
                        emp.user_shift_windows[day7].append((ws7, we7))
                emp.us_two_starts_dow.add(day7)
            else:
                for structure7, b1s, b1e, b2s, b2e in rows7:
                    b1e = b1e if b1e and b1e != time(0, 0) else (time(23, 59) if b1e else None)
                    b2e = b2e if b2e and b2e != time(0, 0) else (time(23, 59) if b2e else None)
                    local_wins = []

                    if b1s and not b1e and b2s and b2e:
                        if _t2m(b2s) - _t2m(b1s) < GAP_MIN:
                            end_cont = _cap_end_from_start(b1s, min(b2e, _plus_minutes(b1s, DAY_MAX_MIN)))
                            if _t2m(end_cont) - _t2m(b1s) < MIN_BLOCK_MIN:
                                end_cont = _plus_minutes(b1s, MIN_BLOCK_MIN)
                            local_wins.append((b1s, end_cont))
                        else:
                            e1 = _plus_minutes(b1s, MIN_BLOCK_MIN)
                            local_wins.append((b1s, e1))
                            start2 = max(b2s, _plus_minutes(e1, GAP_MIN))
                            rem = DAY_MAX_MIN - MIN_BLOCK_MIN
                            e2_cap = _m2t(min(_t2m(b2e), _t2m(start2) + rem))
                            if start2 < e2_cap:
                                local_wins.append((start2, e2_cap))

                    elif b1s and b2s and not b1e and not b2e:
                        if abs(_t2m(b2s) - _t2m(b1s)) < GAP_MIN:
                            end_cont = _cap_end_from_start(b1s, _plus_minutes(b1s, DAY_MAX_MIN))
                            if _t2m(end_cont) - _t2m(b1s) < MIN_BLOCK_MIN:
                                end_cont = _plus_minutes(b1s, MIN_BLOCK_MIN)
                            local_wins.append((b1s, end_cont))
                        else:
                            e1 = _plus_minutes(b1s, MIN_BLOCK_MIN)
                            local_wins.append((b1s, e1))
                            start2 = max(b2s, _plus_minutes(e1, GAP_MIN))
                            late_allow = max(0, DAY_MAX_MIN - MIN_BLOCK_MIN)
                            e2 = _m2t(min(_t2m(start2) + late_allow, 24 * 60 - 1))
                            if start2 < e2:
                                local_wins.append((start2, e2))

                    elif b1s and b1e:
                        e1 = _cap_end_from_start(b1s, b1e)
                        if _t2m(e1) - _t2m(b1s) < MIN_BLOCK_MIN:
                            e1 = _plus_minutes(b1s, MIN_BLOCK_MIN)
                        local_wins.append((b1s, e1))
                        if b2s and b2e:
                            if _t2m(b2s) - _t2m(e1) < GAP_MIN:
                                end_cont = _cap_end_from_start(b1s, b2e)
                                if _t2m(end_cont) > _t2m(e1):
                                    local_wins[-1] = (b1s, end_cont)
                            else:
                                start2 = b2s
                                e2 = _cap_end_from_start(start2, b2e)
                                if start2 < e2:
                                    local_wins.append((start2, e2))

                    elif b1s and not b1e and not b2s and not b2e:
                        e1 = _cap_end_from_start(b1s, _plus_minutes(b1s, DAY_MAX_MIN))
                        if _t2m(e1) - _t2m(b1s) < MIN_BLOCK_MIN:
                            e1 = _plus_minutes(b1s, MIN_BLOCK_MIN)
                        local_wins.append((b1s, e1))

                    elif not b1s and b2s:
                        e2 = _cap_end_from_start(b2s, b2e or _plus_minutes(b2s, DAY_MAX_MIN))
                        if _t2m(e2) - _t2m(b2s) < MIN_BLOCK_MIN:
                            e2 = _plus_minutes(b2s, MIN_BLOCK_MIN)
                        local_wins.append((b2s, e2))

                    for ws7, we7 in local_wins:
                        if ws7 < we7:
                            emp.user_shift_windows[day7].append((ws7, we7))
                    if b1s and b2s: emp.us_two_starts_dow.add(day7)

        # Fallback: día SIN UserShift → desde ShiftType windows
        for e in emps:
            for dow in range(7):
                if e.user_shift_windows.get(dow): continue
                raw = e.shift_type_windows.get(dow, [])
                wins = sorted(list({(w[0], w[1]) for w in raw}), key=lambda w: _t2m(w[0]))
                if not wins: continue
                if len(wins) >= 2:
                    (s1, e1), (s2, e2) = wins[0], wins[1]
                    if _t2m(s2) - _t2m(s1) < GAP_MIN:
                        end_cont = _m2t(min(_t2m(e2), _t2m(s1) + DAY_MAX_MIN))
                        if _t2m(end_cont) - _t2m(s1) < MIN_BLOCK_MIN:
                            end_cont = _plus_minutes(s1, MIN_BLOCK_MIN)
                        if s1 < end_cont:
                            e.user_shift_windows[dow].append((s1, end_cont))
                    else:
                        e1_eff = _m2t(min(_t2m(e1), _t2m(s1) + DAY_MAX_MIN))
                        if _t2m(e1_eff) - _t2m(s1) < MIN_BLOCK_MIN:
                            e1_eff = _plus_minutes(s1, MIN_BLOCK_MIN)
                        if s1 < e1_eff:
                            e.user_shift_windows[dow].append((s1, e1_eff))
                        start2 = max(s2, _plus_minutes(e1_eff, GAP_MIN))
                        rem = max(0, DAY_MAX_MIN - (_t2m(e1_eff) - _t2m(s1)))
                        e2_eff = _m2t(min(_t2m(e2), _t2m(start2) + rem))
                        if start2 < e2_eff:
                            e.user_shift_windows[dow].append((start2, e2_eff))
                        e.us_two_starts_dow.add(dow)
                else:
                    s1, e1 = wins[0]
                    e1_eff = _m2t(min(_t2m(e1), _t2m(s1) + DAY_MAX_MIN))
                    if _t2m(e1_eff) - _t2m(s1) < MIN_BLOCK_MIN:
                        e1_eff = _plus_minutes(s1, MIN_BLOCK_MIN)
                    if s1 < e1_eff:
                        e.user_shift_windows[dow].append((s1, e1_eff))
                if e.shift_type_restr_by_dow.get(dow):
                    e.user_shifts[dow] |= set(e.shift_type_restr_by_dow[dow])

        reglas = {
            "min_duracion_turno_horas": MIN_SHIFT_DURATION_HOURS,
            "min_descanso_entre_turnos_horas": MIN_HOURS_BETWEEN_SHIFTS,
            "min_gap_split_horas": MIN_HOURS_BETWEEN_SPLIT,
            "max_horas_por_dia": MAX_HOURS_PER_DAY,
            "dias_descanso_semana": MIN_DAYS_OFF,
            "max_dias_trabajo_semana": MAX_DAYS_PER_WEEK,
            "max_bloques_por_dia": 2,
        }

        print(f"[DATA] {len(emps)} empleados, {len(demands)} demands OK")
        return emps, demands, (tpl_id, tpl_name), week, shift_types, reglas


# ═══════════════════════════════════════════════════════════════════
# OBSERVATION + COALESCE HELPERS
# ═══════════════════════════════════════════════════════════════════

def build_latest_end_map_from_demands(demands):
    result = defaultdict(dict)
    for dm in demands:
        dk = dm.date.isoformat()
        ws_key = str(dm.wsid) if dm.wsid else None
        if ws_key is None: continue
        e_min = _t2m(_end_eff(dm.end))
        if ws_key not in result[dk] or e_min > result[dk][ws_key]:
            result[dk][ws_key] = e_min
    return dict(result)

def build_latest_end_of_day_map(demands):
    result = {}
    for dm in demands:
        dk = dm.date.isoformat()
        e_min = _t2m(_end_eff(dm.end))
        if dk not in result or e_min > result[dk]: result[dk] = e_min
    return result

def coalesce_employee_day_workstation(assigns_day):
    by_key = defaultdict(list)
    for emp, dm in assigns_day:
        if dm.wsid is None:
            by_key[(emp.id, None)].append((emp, _t2m(dm.start), _t2m(_end_eff(dm.end)), [dm]))
            continue
        s, e = _t2m(dm.start), _t2m(_end_eff(dm.end))
        by_key[(emp.id, dm.wsid)].append((emp, s, e, [dm]))
    merged = {}
    for (eid, wsid), rows in by_key.items():
        rows.sort(key=lambda x: (x[1], x[2]))
        out = []
        cur_emp, cs, ce, src = rows[0][0], rows[0][1], rows[0][2], rows[0][3][:]
        for _, s, e, src_dms in rows[1:]:
            if s <= ce:
                ce = max(ce, e); src.extend(src_dms)
            else:
                out.append((cur_emp, cs, ce, src))
                cur_emp, cs, ce, src = rows[0][0], s, e, src_dms[:]
        out.append((cur_emp, cs, ce, src))
        merged[(eid, wsid)] = out
    return merged


# ═══════════════════════════════════════════════════════════════════
# GENERATE (IA + UserShift + Hybrid)
# ═══════════════════════════════════════════════════════════════════

def generate_ai(week_start: date):
    emps, demands, (tpl_id, tpl_name), week, shift_types, reglas = load_data(week_start)

    # ── PLAN USERSHIFT MODES (NUEVO) ──
    overrides, usershift_plan = plan_usershift_day_modes(emps, demands, week)

    # ── ENTRENAR/CARGAR MODELO IA ──
    from services.aprendizaje_historico import AprendizajeHistoricoService
    ai_svc = AprendizajeHistoricoService(debug=True)
    csv_path = CSV_ENTRENAMIENTO if os.path.exists(CSV_ENTRENAMIENTO) else None
    if csv_path:
        print(f"[AI] Entrenando desde CSV: {csv_path}")
        ai_svc.entrenar_desde_csv(csv_path)
    else:
        print("[AI] CSV no encontrado, modelo vacío")
        ai_svc._modelo = ModeloPatrones()
    modelo = ai_svc.modelo

    # ── GENERAR SCHEDULE (con overrides) ──
    generator = AIScheduleGenerator(modelo=modelo, reglas=reglas, debug=True)
    sched, coverage_stats, days_off_diag = generator.generar(
        emps=emps, demands=demands, week=week,
        overrides=overrides,  # ← AHORA se pasan los overrides
    )

    # ── HYBRID 0.5 POSTPROCESS (NUEVO) ──
    apply_hybrid_05_postprocess(emps, demands, week, sched, coverage_stats, overrides)

    # ── AUSENCIAS ──
    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id": uid(), "wsid": None, "wsname": "AUSENCIA",
                    "start": time(0, 0), "end": time(0, 0), "date": d,
                    "shift_type": None, "is_hybrid_05": False,
                })()
                sched[d].append((emp, pseudo_dm))

    # ── BUILD RESPONSE JSON ──
    total_req = sum(dm.need for dm in demands)
    total_cov = sum(cs["covered"] for cs in coverage_stats.values())
    total_unmet = sum(cs["unmet"] for cs in coverage_stats.values())

    latest_end_by_wsid = build_latest_end_map_from_demands(demands)
    latest_end_by_day = build_latest_end_of_day_map(demands)

    res = {
        "template": (tpl_id, tpl_name),
        "week_start": week_start.isoformat(),
        "week_end": (week_start + timedelta(days=6)).isoformat(),
        "latest_end_by_wsid": latest_end_by_wsid,
        "latest_end_of_day": latest_end_by_day,
        "coverage_pct": round((total_cov / total_req) * 100, 1) if total_req else 100,
        "summary": {
            "total_employees": len(emps),
            "total_demands": total_req,
            "total_covered": total_cov,
            "total_unmet": total_unmet,
            "days_off_violations": days_off_diag,
            "coverage": round((total_cov / total_req) * 100, 1) if total_req else 100,
            "flexible_mode": True,
            "solver": "ai_pattern_v4.1",
        },
        "coverage_details": {
            d_id: {
                "workstation": s["demand"].wsname,
                "date": s["demand"].date.isoformat(),
                "time": f"{s['demand'].start.strftime('%H:%M')}-{s['demand'].end.strftime('%H:%M')}",
                "demanded": s["demand"].need,
                "covered": s["covered"],
                "unmet": s["unmet"],
                "coverage_pct": s["coverage_pct"],
            } for d_id, s in coverage_stats.items()
        },
        "schedule": {},
    }

    for d in week:
        k = d.isoformat()
        res["schedule"][k] = []
        for emp, dm in sorted(sched.get(d, []),
                              key=lambda x: (x[0].name, x[1].wsname, _t2m(x[1].start))):
            day_key = d.isoformat()
            ws_latest = (latest_end_by_wsid.get(day_key, {}) or {}).get(str(dm.wsid)) if dm.wsid else None
            last_day = latest_end_by_day.get(day_key)
            cur_end_min = _t2m(_end_eff(dm.end))

            if dm.wsid is None:
                obs = emp.abs_reason.get(d, "ABS")
            elif ws_latest is not None and cur_end_min == ws_latest:
                obs = "C"
            elif last_day is not None and cur_end_min == last_day:
                obs = ""
            else:
                obs = "BT"

            res["schedule"][k].append({
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "workstation_id": str(dm.wsid) if dm.wsid else None,
                "workstation_name": dm.wsname,
                "start_time": dm.start.strftime("%H:%M") if dm.start else None,
                "end_time": dm.end.strftime("%H:%M") if dm.end else None,
                "observation": obs,
            })

    return res, sched, emps, week, demands, coverage_stats


# ═══════════════════════════════════════════════════════════════════
# CLEANUP
# ═══════════════════════════════════════════════════════════════════

def cleanup_null_workstation_schedules(cur, ws, we):
    try:
        cur.execute('''
            DELETE FROM "Management"."Schedules"
            WHERE "Date" BETWEEN %s AND %s
              AND "WorkstationId" IS NULL AND "StartTime" IS NULL AND "EndTime" IS NULL
              AND "Observation" NOT IN ('ABS','VAC')
        ''', (ws, we))
        return cur.rowcount
    except: return 0


# ═══════════════════════════════════════════════════════════════════
# ENDPOINTS
# ═══════════════════════════════════════════════════════════════════

@app.route('/api/health')
def health():
    st = {"status": "checking", "timestamp": now().isoformat(), "version": "4.2-ai-feedback", "checks": {}}
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute("SELECT version()")
            st["checks"]["database"] = {"status": "healthy", "version": cur.fetchone()[0].split(',')[0]}
            st["status"] = "healthy"
    except Exception as e:
        st["checks"]["database"] = {"status": "unhealthy", "message": str(e)}
        st["status"] = "unhealthy"
    return jsonify(st), (200 if st["status"] == "healthy" else 503)


@app.route('/api/agenda/preview')
def preview():
    wk = request.args.get('week_start')
    if not wk: return jsonify({"error": "Falta week_start"}), 400
    try: ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError: return jsonify({"error": "Fecha inválida"}), 400
    try:
        res, _, _, _, _, _ = generate_ai(ws)
        return jsonify(res), 200
    except (DatabaseConnectionError, DataNotFoundError) as e:
        return jsonify({"error": str(e)}), 400


@app.route('/api/agenda/save', methods=['POST'])
def save():
    data = request.get_json() or {}
    wk = data.get('week_start')
    force = bool(data.get('force', False))
    if not wk: return jsonify({"error": "Falta week_start"}), 400
    try: ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError: return jsonify({"error": "Fecha inválida"}), 400

    we = ws + timedelta(days=6)
    token = data.get("token") or f"{ws.isoformat()}|ai|{uid()[:8]}"

    try:
        res, sched, emps, week, demands, coverage_stats = generate_ai(ws)
    except (DatabaseConnectionError, DataNotFoundError) as e:
        return jsonify({"error": str(e)}), 400

    inserted_gaps = 0; inserted_quality = 0
    sugerencias_generadas = []; ajustes_ia = []

    try:
        with conn() as c, c.cursor() as cur:
            cur.execute('SELECT COUNT(*) FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s', (ws, we))
            if cur.fetchone()[0] and not force:
                return jsonify({"error": "Horario ya existe para esa semana"}), 409

            if force:
                cur.execute('DELETE FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s', (ws, we))
                for tbl, col in [("ScheduleGaps", "Date"), ("ScheduleQualityShiftScores", "Date"),
                                  ("ScheduleSuggestions", "WeekStart")]:
                    try: cur.execute(f'DELETE FROM "Management"."{tbl}" WHERE "{col}" BETWEEN %s AND %s', (ws, we))
                    except: pass
                try: cur.execute('DELETE FROM "Management"."AIPredictions" WHERE "Token" LIKE %s', (f"{ws.isoformat()}%",))
                except: pass

            # ═══════════════════════════════════════════════════════════
            # v4.2 FLUJO MEJORADO: HU 1.1 → HU 1.2 → HU 1.3 → HU 1.6
            # Cada paso alimenta al siguiente con sus resultados
            # ═══════════════════════════════════════════════════════════

            explicaciones = []
            quality_result = {}

            # ═════ HU 1.1 GAPS (explicador de huecos) ═════
            cur.execute("SAVEPOINT hu11")
            try:
                from services.explicador_huecos import ExplicadorHuecosService, ContextoExplicacion
                asignaciones_por_empleado = defaultdict(list)
                for d0 in sorted(sched.keys()):
                    for emp0, dm0 in sched[d0]:
                        if dm0 is None or dm0.wsid is None: continue
                        ini0 = datetime.combine(d0, dm0.start)
                        fin0 = datetime.combine(d0, dm0.end)
                        if dm0.end == time(0, 0) or fin0 <= ini0:
                            fin0 = datetime.combine(d0 + timedelta(days=1), dm0.end)
                        asignaciones_por_empleado[emp0].append((ini0, fin0, dm0.wsid))
                ctx = ContextoExplicacion(empleados=emps, asignaciones_por_empleado=asignaciones_por_empleado)
                explicador = ExplicadorHuecosService(cursor=cur, debug=True)
                explicaciones = explicador.generar_y_guardar(
                    agenda_result=res,
                    ctx=ctx,
                    token=token,
                    is_post_ai=True,
                )
                inserted_gaps = len(explicaciones)
                print(f"[HU1.1] {inserted_gaps} gaps guardados en BD")
                cur.execute("RELEASE SAVEPOINT hu11")
            except Exception as e:
                try: cur.execute("ROLLBACK TO SAVEPOINT hu11")
                except: pass
                try: cur.execute("RELEASE SAVEPOINT hu11")
                except: pass
                print(f"[HU1.1] Error: {e}"); import traceback; traceback.print_exc()

            # ═════ HU 1.2 QUALITY (puntaje por turno) ═════
            cur.execute("SAVEPOINT hu12")
            try:
                from services.puntaje_calidad_turno import ScheduleQualityService
                quality_svc = ScheduleQualityService(cur)
                # v4.2: Pasar coverage_stats completo para guardar detalle por slot
                quality_result = quality_svc.calcular_y_guardar(
                    token=token, ws=ws, we=we,
                    res={"unmet_demands": [
                        {"required": cs["demand"].need, "covered": cs["covered"], "unmet": cs["unmet"]}
                        for cs in coverage_stats.values()]},
                    sched=sched, emps=emps,
                    coverage_stats=coverage_stats,
                    is_post_ai=True,
                )
                inserted_quality = quality_result.get("inserted", 0)
                print(f"[HU1.2] Score={quality_result.get('score', 0):.2f}, {inserted_quality} registros en BD")
                cur.execute("RELEASE SAVEPOINT hu12")
            except Exception as e:
                try: cur.execute("ROLLBACK TO SAVEPOINT hu12")
                except: pass
                try: cur.execute("RELEASE SAVEPOINT hu12")
                except: pass
                print(f"[HU1.2] Error: {e}"); import traceback; traceback.print_exc()

            # ═════ HU 1.3 SUGGESTIONS (sugerencias) ═════
            cur.execute("SAVEPOINT hu13")
            try:
                from services.sugerencias_mejora import SugerenciasMejoraService
                sug_svc = SugerenciasMejoraService(cursor=cur, debug=True)
                # v4.2: Pasar las explicaciones COMPLETAS de HU 1.1 (no raw gaps)
                # para que tenga categorías, razones, etc.
                sugerencias_generadas = sug_svc.generar_y_guardar(
                    gaps=explicaciones,  # ← AHORA recibe explicaciones completas de HU 1.1
                    sched=sched,
                    emps=emps,
                    quality_result=quality_result,  # ← AHORA recibe resultado de HU 1.2
                    token=token,
                    week_start=ws,
                    week_end=we,
                    is_post_ai=True,
                )
                print(f"[HU1.3] {len(sugerencias_generadas)} sugerencias guardadas en BD")
                cur.execute("RELEASE SAVEPOINT hu13")
            except Exception as e:
                try: cur.execute("ROLLBACK TO SAVEPOINT hu13")
                except: pass
                try: cur.execute("RELEASE SAVEPOINT hu13")
                except: pass
                print(f"[HU1.3] Error: {e}"); import traceback; traceback.print_exc()

            # ═════ HU 1.6 VALIDATION (validador de reglas) ═════
            cur.execute("SAVEPOINT hu16")
            try:
                from services.validador_reglas import ValidadorReglasService
                val_svc = ValidadorReglasService(cursor=cur, debug=True)
                val_result = val_svc.validar_y_guardar(
                    sched=sched, token=token, week_start=ws, week_end=we,
                    emps=emps, is_post_ai=True)
                print(f"[HU1.6] {val_result.total_violaciones} violaciones")
                res["summary"]["hu16_violations"] = val_result.total_violaciones
                res["summary"]["hu16_schedule_valid"] = val_result.schedule_valido
                cur.execute("RELEASE SAVEPOINT hu16")
            except Exception as e:
                try: cur.execute("ROLLBACK TO SAVEPOINT hu16")
                except: pass
                try: cur.execute("RELEASE SAVEPOINT hu16")
                except: pass
                print(f"[HU1.6] Error: {e}")

            # ═════ INSERT SCHEDULES ═════
            latest_end_by_wsid = res.get("latest_end_by_wsid", {})
            latest_end_by_day = res.get("latest_end_of_day", {})
            MIN_BLOCK_SAVE_MIN = MIN_SHIFT_DURATION_HOURS * 60

            for d in week:
                ass = sched.get(d, [])
                if not ass: continue
                for emp, dm in ass:
                    if dm is None or dm.wsid is None:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation","IsDeleted","DateCreated","Token")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (uid(), d, str(emp.id), None, None, None,
                              emp.abs_reason.get(d, 'ABS'), False, now(), token))

                coalesced = coalesce_employee_day_workstation(ass)
                total_min_by_eid = defaultdict(int)
                for (eid, wsid), rows in coalesced.items():
                    if wsid is None: continue
                    for emp, s, e, _ in rows: total_min_by_eid[eid] += max(0, e - s)

                for (eid, wsid), rows in coalesced.items():
                    if wsid is None: continue
                    if total_min_by_eid.get(eid, 0) < MIN_BLOCK_SAVE_MIN:
                        if ASCII_LOGS:
                            nm = rows[0][0].name if rows else eid
                            print(f"[SAVE-MIN] {d} omitido {nm}: {total_min_by_eid.get(eid,0)/60:.1f}h<{MIN_SHIFT_DURATION_HOURS}h")
                        continue
                    for emp, s_min, e_min, src_dms in rows:
                        if e_min <= s_min: continue
                        s_t = _m2t(s_min)
                        e_t = _m2t(e_min if e_min < 1440 else 0)
                        day_key = d.isoformat()
                        ws_latest = (latest_end_by_wsid.get(day_key, {}) or {}).get(str(wsid))
                        last_day = latest_end_by_day.get(day_key)
                        if ws_latest is not None and e_min == ws_latest: obs = "C"
                        elif last_day is not None and e_min == last_day: obs = ""
                        else: obs = "BT"
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation",
                                 "IsDeleted","DateCreated","Token")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (uid(), d, str(emp.id), str(wsid),
                              timedelta(hours=s_t.hour, minutes=s_t.minute),
                              timedelta(hours=e_t.hour, minutes=e_t.minute),
                              obs, False, now(), token))

            # ═════ HU 1.4 POST-SAVE TRAINING (con feedback loop v4.2) ═════
            cur.execute("SAVEPOINT hu14")
            try:
                from services.aprendizaje_historico import AprendizajeHistoricoService

                ai_post = AprendizajeHistoricoService(cur, debug=True)
                t_start = ws - timedelta(days=84)

                ai_post.entrenar_desde_bd(t_start, we)
                mid = ai_post.guardar_modelo(nombre="auto", version=f"auto-{ws.isoformat()}")

                coverage_pct = float(res.get("coverage_pct", 0))
                notes_parts = [f"post-save {token}"]
                if quality_result:
                    notes_parts.append(f"score={quality_result.get('score', 0):.1f}")
                notes_parts.append(f"gaps={inserted_gaps}")
                notes_parts.append(f"sugs={len(sugerencias_generadas) if sugerencias_generadas else 0}")

                ai_post.registrar_training_history(
                    model_id=mid,
                    data_start=t_start,
                    data_end=we,
                    notes=" | ".join(notes_parts),
                    coverage_improvement=coverage_pct
                )

                print(f"[HU1.4] Modelo guardado: {mid} (con feedback de gaps/quality/suggestions)")
                cur.execute("RELEASE SAVEPOINT hu14")

            except Exception as e:
                try:
                    cur.execute("ROLLBACK TO SAVEPOINT hu14")
                except Exception:
                    pass

                try:
                    cur.execute("RELEASE SAVEPOINT hu14")
                except Exception:
                    pass

                print(f"[HU1.4] Error REAL: {e}")
                import traceback
                traceback.print_exc()

            cleanup_null_workstation_schedules(cur, ws, we)
            c.commit()

    except Exception as e:
        import traceback; traceback.print_exc()
        return jsonify({"error": "Error al guardar", "detail": str(e)}), 500

    out = dict(res) if isinstance(res, dict) else {"result": res}
    out.setdefault("summary", {})
    out["summary"]["token"] = token
    out["summary"]["hu11_gaps_inserted"] = inserted_gaps
    out["summary"]["hu12_quality_rows_inserted"] = inserted_quality
    out["summary"]["hu13_suggestions_generated"] = len(sugerencias_generadas) if sugerencias_generadas else 0
    out["summary"]["hu14_ai_adjustments"] = len(ajustes_ia) if ajustes_ia else 0

    return jsonify({"message": "Horario guardado (IA v4.2)", **out}), 201


logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
if __name__ == "__main__":
    print("API Gandarias v4.2 (IA + feedback loop) en http://localhost:5000")
    print(f"CSV entrenamiento: {CSV_ENTRENAMIENTO}")
    app.run(host="0.0.0.0", port=5000, debug=False)