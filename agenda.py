#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGENDA GENERATOR API – Gandarías v3.14 (determinista + reglas split + fallback greedy)
• Intento flexible con CP-SAT. Si el modelo no es factible, caemos a planificador GREEDY de emergencia.
• UserShifts obligatorios si el día del empleado tiene ≥4h viables dentro de sus ventanas (y ST compatibles);
  si no, el día pasa a “asignación libre” (override) y se reporta el motivo en el summary.
• 0–5 SIEMPRE (día libre, ventanas, excepciones, ausencias).
• Cortes solo en los BORDES de cada UserShift: 12–14 ⇒ 12–13 y 13–14.
• Determinismo: random_seed=0, num_search_workers=1, SQL con ORDER BY y bucles ordenados.
"""

import logging
import uuid
from collections import defaultdict
from datetime import date, datetime, time, timedelta, timezone
from typing import List, Tuple, Dict, Set

import psycopg2
from flask import Flask, jsonify, request
from flask_cors import CORS
from ortools.sat.python import cp_model
from psycopg2 import DataError, OperationalError, ProgrammingError

# ───────── CONFIG GENERAL ─────────
ASCII_LOGS = True
ENFORCE_PEAK_CAP = True
PEAK_CAP_LOG = True
MIN_HOURS_BETWEEN_SHIFTS = 9
MIN_HOURS_BETWEEN_SPLIT = 3     # ← se sobreescribe desde BD (regla adicional)
MAX_DAYS_PER_WEEK = 6
MAX_HOURS_PER_DAY = 9
MIN_SHIFT_DURATION_HOURS = 4
HARD_REQUIRE_USERSHIFT = True

# Pesos
WEIGHT_MUST_HAVE_ONE = 200_000
WEIGHT_ULTRA_SLOT0   = 500_000
WEIGHT_SHORT_SLOT    = 100_000
WEIGHT_CONSOLIDATE   = 250
WEIGHT_USERWINDOW    = 80_000

# ───────── FLASK ─────────
app = Flask(__name__)
CORS(app)

# ───────── BD ─────────
DB = {
    "host":     "database-gandarias.ct6gmyi80fdr.eu-central-1.rds.amazonaws.com",
    "port":     5432,
    "dbname":   "postgres",
    "user":     "postgres",
    "password": "MyStrongPassword!123_",
    "sslmode":  "require",
}

def uid(): return str(uuid.uuid4())
def now(): return datetime.now(timezone.utc)

# ───────── EXCEPCIONES ─────────
class DatabaseConnectionError(Exception): ...
class DataNotFoundError(Exception): ...
class DataIntegrityError(Exception): ...
class ScheduleGenerationError(Exception): ...

# ───────── MODELOS ─────────
class Emp:
    def __init__(self, row: Tuple):
        self.id, self.name, self.split = row
        self.roles: Set = set()
        self.day_off: Set[int] = set()            # 0=Lun..6=Dom
        self.window = defaultdict(list)           # DOW → [(from,to)]
        self.exc = defaultdict(list)              # date → [(from,to)]
        self.absent: Set[date] = set()
        self.abs_reason: Dict[date, str] = {}

        self.user_shifts = defaultdict(set)       # DOW → {ShiftTypeId}
        self.user_shift_windows = defaultdict(list)  # DOW → [(start,end)]
        self.shift_type_restrictions = set()

    def can(self, ws): return ws in self.roles
    def off(self, d: date) -> bool: return d.weekday() in self.day_off
    def absent_day(self, d: date) -> bool: return d in self.absent

    def available(self, d: date, s: time, e: time) -> bool:
        # 0–5 SIEMPRE
        if self.off(d) or self.absent_day(d): return False
        if not self.day_off and not self.window and not self.exc: return True
        win = self.exc.get(d) or self.window.get(d.weekday())
        if not win: return False
        end = e if e != time(0,0) else time(23,59)
        for a,b in win:
            b2 = b if b != time(0,0) else time(23,59)
            if s >= a and end <= b2: return True
        return False

class Demand:
    def __init__(self, row: Tuple):
        (self.id, rdate, self.wsid, self.wsname, self.start, self.end, need) = row
        self.date = rdate.date() if hasattr(rdate, 'date') else rdate
        self.need = int(need)
        self.slot_index = 0
        self.shift_type = None

# ───────── HELPERS ─────────
def _t2m(t: time) -> int:
    if t is None: return 0
    return 24*60 if t == time(0,0) else (t.hour*60 + t.minute)

def _m2t(m: int) -> time:
    m = max(0, min(24*60, m))
    return time(m//60, m%60) if m < 24*60 else time(0,0)

def duration_min(dm) -> int:
    s = _t2m(dm.start)
    e = _t2m(dm.end) if dm.end != time(0,0) else 24*60
    if e < s: e += 24*60
    return e - s

def to_min(t: time) -> int: return t.hour*60 + t.minute
def overlap(a, b): return not (a.end <= b.start or b.end <= a.start)

def monday(d: date) -> date:
    while d.weekday() != 0: d -= timedelta(days=1)
    return d

# ───────── DB helpers ─────────
def conn():
    try:
        return psycopg2.connect(**DB)
    except OperationalError as e:
        t = str(e)
        if "could not connect" in t: raise DatabaseConnectionError("No se puede conectar al servidor de BD")
        if "authentication failed" in t: raise DatabaseConnectionError("Credenciales de BD incorrectas")
        raise DatabaseConnectionError(t)

def fetchall(cur, sql, pars=None):
    try:
        if pars is None:
            cur.execute(sql)
        else:
            cur.execute(sql, pars)
        return cur.fetchall()
    except (ProgrammingError, DataError) as e:
        raise DataIntegrityError(str(e))

# ───────── DEMAND PROCESSING ─────────
def split_long_segment(d: date, wsid, wsname, s_min: int, e_min: int, need: int, max_hours: int):
    out = []
    limit = max_hours * 60
    cur = s_min
    while cur < e_min:
        nxt = min(cur + limit, e_min)
        out.append(Demand((uid(), d, wsid, wsname, _m2t(cur), _m2t(nxt if nxt < 24*60 else 0), need)))
        cur = nxt
    return out

def coalesce_demands(demands, tolerate_gap_min: int = 0):
    by_key = defaultdict(list)
    for d in demands: by_key[(d.date, d.wsid, d.wsname)].append(d)
    merged = []
    for (dte, wsid, wsname), items in by_key.items():
        items.sort(key=lambda x: (_t2m(x.start), _t2m(x.end)))
        if not items: continue
        curr = items[0]
        for nxt in items[1:]:
            pot_dur_min = _t2m(nxt.end if nxt.end != time(0,0) else time(23,59)) - _t2m(curr.start)
            pot_dur_h = pot_dur_min / 60.0
            if (nxt.need == curr.need
                and _t2m(nxt.start) - _t2m(curr.end) <= tolerate_gap_min
                and pot_dur_h <= MAX_HOURS_PER_DAY):
                curr.end = nxt.end
            else:
                merged.append(curr); curr = nxt
        merged.append(curr)
    return [Demand((d.id, d.date, d.wsid, d.wsname, d.start, d.end, d.need)) for d in merged]

def normalize_by_max_need_profile(demands):
    if not ENFORCE_PEAK_CAP: return demands
    grouped = defaultdict(list)
    for d in demands: grouped[(d.date, d.wsid, d.wsname)].append(d)
    out = []
    for (dte, wsid, wsname), items in grouped.items():
        cuts = set()
        for it in items:
            s = _t2m(it.start); e = _t2m(it.end) if it.end != time(0,0) else 24*60
            cuts.add(s); cuts.add(e)
        cuts = sorted(cuts)
        if len(cuts) <= 1: continue
        segments = []
        over_sum_detected = False
        for i in range(len(cuts)-1):
            a, b = cuts[i], cuts[i+1]
            if a >= b: continue
            active = []
            for it in items:
                s = _t2m(it.start); e = _t2m(it.end) if it.end != time(0,0) else 24*60
                if s <= a and e >= b: active.append(it.need)
            if not active: continue
            max_need = max(active)
            sum_need = sum(active)
            if sum_need > max_need: over_sum_detected = True
            segments.append((a, b, max_need))
        fused = []
        for seg in segments:
            if not fused: fused.append(seg)
            else:
                la, lb, ln = fused[-1]; a, b, n = seg
                if ln == n and a == lb: fused[-1] = (la, b, n)
                else: fused.append(seg)
        for a, b, n in fused:
            if n <= 0 or a >= b: continue
            if (b - a) <= MAX_HOURS_PER_DAY * 60:
                out.append(Demand((uid(), dte, wsid, wsname, _m2t(a), _m2t(b if b < 24*60 else 0), n)))
            else:
                out.extend(split_long_segment(dte, wsid, wsname, a, b, n, MAX_HOURS_PER_DAY))
        if over_sum_detected and PEAK_CAP_LOG:
            print(f"[NORMALIZACION] {dte} {wsname}: solapes reducidos usando MAX(need).")
    return out

def set_slot_indexes(demands):
    by_day_ws = defaultdict(list)
    for d in demands: by_day_ws[(d.date, d.wsid)].append(d)
    for lst in by_day_ws.values():
        lst.sort(key=lambda x: (_t2m(x.start), _t2m(x.end)))
        for idx, d in enumerate(lst): d.slot_index = idx

# ───────── Cortes por bordes de UserShift ─────────
def build_extra_cuts_from_usershifts_edges_only(emps: Dict[str, Emp], week: List[date]):
    extra = defaultdict(set)
    for emp in emps.values():
        for dow, wins in emp.user_shift_windows.items():
            for d in week:
                if d.weekday() != dow: continue
                for w_s, w_e in wins:
                    s = _t2m(w_s); e = _t2m(w_e)
                    if e > s:
                        extra[d].add(s)
                        extra[d].add(e)
    return extra

def normalize_with_extra_cuts(demands: List[Demand], extra_cuts_by_date: Dict[date, Set[int]],
                              max_hours: int = MAX_HOURS_PER_DAY,
                              peak_cap: bool = ENFORCE_PEAK_CAP,
                              log_cap: bool = PEAK_CAP_LOG):
    out = []
    for dm in demands:
        d = dm.date
        cuts = sorted(extra_cuts_by_date.get(d, set()))
        s = _t2m(dm.start)
        e = _t2m(dm.end) if dm.end != time(0,0) else 24*60
        if e <= s: e += 24*60
        inner = [c for c in cuts if s < c < e]
        points = [s] + inner + [e]
        for i in range(len(points)-1):
            a, b = points[i], points[i+1]
            if b - a <= 0: continue
            segs = split_long_segment(dm.date, dm.wsid, dm.wsname, a, b, dm.need, max_hours)
            out.extend(segs)
    return out

# ───────── SHIFTTYPES & checks ─────────
def demand_matches_shifttype(demand: Demand, st) -> bool:
    ds = _t2m(demand.start)
    de = _t2m(demand.end) if demand.end != time(0,0) else 24*60
    ss = _t2m(st['start_time'])
    se = _t2m(st['end_time']) if st['end_time'] != time(0,0) else 24*60
    return (ss <= ds and de <= se)

def get_shifttype_for_demand(demand: Demand, shift_types: list):
    for st in shift_types:
        if demand_matches_shifttype(demand, st):
            return st
    return None

def employee_can_work_demand_with_shifts(emp: Emp, demand: Demand, dow: int) -> tuple:
    end = demand.end if demand.end != time(0,0) else time(23,59)
    if emp.user_shift_windows.get(dow):
        in_window = False
        for w_s, w_e in emp.user_shift_windows[dow]:
            w_end = w_e if w_e != time(0,0) else time(23,59)
            if demand.start >= w_s and end <= w_end:
                in_window = True; break
        if not in_window: return False, "outside_usershift_window"
    if hasattr(demand, 'shift_type') and demand.shift_type:
        if demand.shift_type['id'] not in emp.user_shifts.get(dow, set()):
            return False, "shift_type_not_allowed"
    return True, "ok"

def inside_usershift_window(emp: Emp, dm: Demand, overrides: Set[Tuple[str, date]]) -> bool:
    """True si la asignación cae dentro de alguna ventana de UserShift del empleado ese día.
       Si ese día está en overrides (asignación libre), no priorizamos ventanas."""
    dday = dm.date
    if (emp.id, dday) in overrides:
        return False
    wins = emp.user_shift_windows.get(dday.weekday(), [])
    if not wins:
        return False
    end = dm.end if dm.end != time(0,0) else time(23,59)
    for ws, we in wins:
        w_end = we if we != time(0,0) else time(23,59)
        if dm.start >= ws and end <= w_end:
            # si hay ShiftType en la demanda, también debe ser compatible
            if dm.shift_type and dm.shift_type['id'] not in emp.user_shifts.get(dday.weekday(), set()):
                return False
            return True
    return False


def _usershift_day_eligibility(emp: Emp, ddate: date) -> tuple:
    """
    Devuelve (ok: bool, kind: 'single'|'split'|None, reason: str).
    - 'single': un bloque continuo ≥4h
    - 'split' : dos bloques, cada uno ≥4h y gap ≥ MIN_HOURS_BETWEEN_SPLIT
    """
    dow = ddate.weekday()
    wins = sorted(emp.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1])))
    if not wins:
        return False, None, "no_usershift_for_day"

    # fusionar solapes
    merged = []
    for s,e in wins:
        smin, emin = _t2m(s), _t2m(e if e != time(0,0) else time(23,59))
        if not merged or smin > merged[-1][1]:
            merged.append([smin, emin])
        else:
            merged[-1][1] = max(merged[-1][1], emin)

    if len(merged) == 1:
        if (merged[0][1] - merged[0][0]) >= MIN_SHIFT_DURATION_HOURS * 60:
            return True, "single", "ok"
        return False, None, "usershift_block_lt_4h"

    if len(merged) >= 2:
        a, b = merged[0], merged[1]
        dur_a = a[1] - a[0]
        dur_b = b[1] - b[0]
        gap   = b[0] - a[1]
        if (dur_a >= MIN_SHIFT_DURATION_HOURS*60 and
            dur_b >= MIN_SHIFT_DURATION_HOURS*60 and
            gap   >= MIN_HOURS_BETWEEN_SPLIT*60):
            return True, "split", "ok"
        return False, None, "usershift_split_not_valid"

    return False, None, "usershift_structure_unsupported"


# ───────── TEMPLATE PICKER ─────────
def pick_template(cur, week_start: date, week_end: date):
    act = fetchall(cur, '''
        SELECT "Id","Name"
        FROM "Management"."WorkstationDemandTemplates"
        WHERE "IsActive" = TRUE
    ''')
    if len(act) == 1: return act[0]
    if len(act) > 1: raise DataIntegrityError("Hay varias plantillas activas; debe haber solo una")

    rows = fetchall(cur, '''
        SELECT "Id","Name","StartDate"::date,"EndDate"::date,
               COALESCE("DateCreated", '-infinity'::timestamptz) AS created,
               (SELECT COUNT(*) FROM "Management"."WorkstationDemands" d WHERE d."TemplateId" = t."Id") AS demandas
        FROM "Management"."WorkstationDemandTemplates" t
        WHERE "StartDate" IS NOT NULL AND "EndDate" IS NOT NULL
        ORDER BY "StartDate","EndDate","Id"
    ''')
    if not rows: raise DataNotFoundError("No existen plantillas con StartDate/EndDate")

    def md(x: date): return (x.month, x.day)
    def same_year(year: int, m: int, d: int) -> date:
        try: return date(year, m, d)
        except ValueError: return date(year, 2, 28) if (m == 2 and d == 29) else date(year, m, d)

    week_end = week_start + timedelta(days=6)
    week_center = week_start + (week_end - week_start) // 2

    def distance_metrics(start_md, end_md):
        y = week_start.year
        s = same_year(y, start_md[0], start_md[1])
        e = same_year(y, end_md[0],   end_md[1])
        segments = [(s, e)] if s <= e else [(s, date(y,12,31)), (date(y,1,1), e)]
        def seg_dist(a, b):
            if not (b < week_start or a > week_end): return (0, 0)
            if b < week_start: return ((week_start - b).days, abs((week_center - b).days))
            else: return ((a - week_end).days, abs((a - week_center).days))
        return min((seg_dist(a, b) for (a, b) in segments), key=lambda x: (x[0], x[1]))

    scored = []
    for tid, name, sdate, edate, created, demandas in rows:
        dist, dcenter = distance_metrics(md(sdate), md(edate))
        scored.append({"id": tid, "name": name, "start": sdate, "end": edate,
                       "created": created, "demandas": int(demandas or 0),
                       "dist": dist, "dcenter": dcenter})
    scored.sort(key=lambda r: (r["dist"], r["dcenter"]))
    chosen = next((r for r in scored if r["demandas"] > 0), None)
    if chosen: return (chosen["id"], chosen["name"])
    raise DataNotFoundError("No se encontró plantilla con demandas > 0")

# ───────── CARGA DATOS ─────────
def load_data(week_start: date):
    week = [week_start + timedelta(days=i) for i in range(7)]
    week_end = week[-1]

    def _to_time(x):
        if x is None: return None
        if isinstance(x, time): return x
        if isinstance(x, timedelta): return (datetime.min + x).time()
        try: return (datetime.min + x).time()
        except Exception: return None

    def _pair(s, e):
        s, e = _to_time(s), _to_time(e)
        if not s or not e: return None
        e = e if e != time(0,0) else time(23,59)
        return (s, e) if s < e else None

    def _complement_blocks(blocks):
        DAY_START, DAY_END = time(0,0), time(23,59)
        ivs = []
        for p in blocks:
            if p: ivs.append(p)
        ivs.sort(key=lambda p: (p[0], p[1]))
        merged = []
        for s, e in ivs:
            if not merged: merged.append([s, e])
            else:
                ls, le = merged[-1]
                if s <= le: merged[-1][1] = max(le, e)
                else: merged.append([s, e])
        out = []
        cur = DAY_START
        for s, e in merged:
            if cur < s: out.append((cur, (s if s != time(0,0) else time(23,59))))
            cur = max(cur, e)
        if cur < DAY_END: out.append((cur, DAY_END))
        return out

    with conn() as c, c.cursor() as cur:
        # 1) Plantilla y demandas
        tpl_id, tpl_name = pick_template(cur, week_start, week_end)
        demands = [Demand(r) for r in fetchall(cur, '''
            SELECT d."Id", %s + d."Day"*interval '1 day',
                   d."WorkstationId", w."Name",
                   (TIMESTAMP '2000-01-01'+d."StartTime")::time,
                   (TIMESTAMP '2000-01-01'+d."EndTime")::time,
                   d."EffortRequired"
            FROM "Management"."WorkstationDemands" d
            JOIN "Management"."Workstations"       w ON w."Id" = d."WorkstationId"
            WHERE d."TemplateId" = %s
            ORDER BY d."Day", d."StartTime", d."EndTime", d."Id"
        ''', (week_start, tpl_id))]
        demands = coalesce_demands(demands, tolerate_gap_min=0)
        demands = normalize_by_max_need_profile(demands)

        # 2) Empleados
        emps_map = {r[0]: Emp(r) for r in fetchall(cur, '''
            SELECT "Id", COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                   COALESCE("ComplementHours", TRUE)
            FROM "Management"."AspNetUsers"
            WHERE "IsActive" AND NOT "IsDelete"
            ORDER BY "LastName","FirstName","Id"
        ''')}
        if not emps_map: raise DataNotFoundError("No hay empleados activos")

        for uid2, ws in fetchall(cur, '''
            SELECT "UserId","WorkstationId"
            FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete"
            ORDER BY "UserId","WorkstationId"
        '''):
            if uid2 in emps_map: emps_map[uid2].roles.add(ws)
        if not any(e.roles for e in emps_map.values()):
            raise DataNotFoundError("Ningún empleado tiene roles asignados")
        emps = [emps_map[k] for k in sorted(emps_map.keys())]

        # 3) Restricciones semanales (0–5)
        for uid3, dow, rt, f1, t1, b1s, b1e, b2s, b2e in fetchall(cur, '''
            SELECT "UserId","DayOfWeek","RestrictionType",
                   "AvailableFrom","AvailableUntil",
                   "Block1Start","Block1End",
                   "Block2Start","Block2End"
            FROM "Management"."EmployeeScheduleRestrictions"
            ORDER BY "UserId","DayOfWeek","RestrictionType"
        '''):
            if uid3 not in emps_map: continue
            emp = emps_map[uid3]
            if rt == 0:
                emp.day_off.add(dow); continue
            if rt == 1:
                emp.window[dow].append((time(0,0), time(23,59))); continue
            if rt == 2:
                s = _to_time(f1); e = _to_time(t1)
                if s is None and e is None: continue
                if s is not None and e is None: e = time(23,59)
                if s is None and e is not None: s = time(0,0)
                if e == time(0,0): e = time(23,59)
                if s < e: emp.window[dow].append((s,e)); continue
            if rt == 3:
                t = _to_time(t1)
                if t: emp.window[dow].append((time(0,0), t if t != time(0,0) else time(23,59))); continue
            if rt == 4:
                p1 = _pair(b1s, b1e); p2 = _pair(b2s, b2e); any_added = False
                if p1: emp.window[dow].append(p1); any_added = True
                if p2: emp.window[dow].append(p2); any_added = True
                if not any_added:
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
                for w in _complement_blocks(blocked):
                    emp.window[dow].append(w)
                continue

        # 4) Excepciones, ausencias
        for uid4, d_exc, rt, f, t in fetchall(cur, '''
            SELECT "UserId","Date","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s
            ORDER BY "UserId","Date","RestrictionType"
        ''', (week_start, week_end)):
            if uid4 not in emps_map: continue
            emp = emps_map[uid4]
            if rt == 0: emp.absent.add(d_exc)
            else:
                s = _to_time(f); e = _to_time(t)
                if s and e and s < e:
                    if e == time(0,0): e = time(23,59)
                    emp.exc[d_exc].append((s, e))

        for uid5, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
            FROM "Management"."Licenses"
            WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
            ORDER BY "UserId","StartDate","EndDate"
        ''', (week_end, week_end, week_end, week_start)):
            if uid5 not in emps_map: continue
            emp = emps_map[uid5]; d0 = max(sd, week_start)
            while d0 <= ed:
                emp.absent.add(d0); emp.abs_reason[d0] = 'VAC'; d0 += timedelta(days=1)

        for uid6, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
            FROM "Management"."UserAbsenteeisms"
            WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
            ORDER BY "UserId","StartDate","EndDate"
        ''', (week_end, week_end, week_end, week_start)):
            if uid6 not in emps_map: continue
            emp = emps_map[uid6]; d0 = max(sd, week_start)
            while d0 <= ed:
                emp.absent.add(d0); emp.abs_reason[d0] = 'ABS'; d0 += timedelta(days=1)

        # 5) ShiftTypes
        shift_types = []
        for row in fetchall(cur, '''
            SELECT "Id","Name","Description",
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time AS start_time,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time AS end_time,
                   "Structure" = 1 AS is_split,
                   "IsActive"
            FROM "Management"."ShiftTypes"
            WHERE "IsActive" = TRUE
            ORDER BY "Name","Id"
        '''):
            shift_types.append({
                'id': row[0], 'name': row[1], 'description': row[2],
                'start_time': row[3], 'end_time': row[4], 'is_split': row[5], 'is_active': row[6]
            })

        # 6) UserShifts  (soporta "abierto" si *_lastStart es NULL ⇒ hasta 23:59)
        for uid7, day, structure, b1s, b1e, b2s, b2e in fetchall(cur, '''
            SELECT "UserId","Day","Structure",
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time,
                   (TIMESTAMP '2000-01-01' + "Block2Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block2lastStart")::time
            FROM "Management"."UserShifts"
            ORDER BY "UserId","Day","Block1Start","Block2Start"
        '''):
            if uid7 not in emps_map:
                continue
            emp = emps_map[uid7]

            # si *_lastStart es NULL ⇒ ventana abierta hasta 23:59
            b1e_eff = (b1e if b1e else time(23,59))
            b2e_eff = (b2e if b2e else time(23,59))

            if b1s and b1s < b1e_eff:
                emp.user_shift_windows[day].append((b1s, b1e_eff))
            if b2s and b2s < b2e_eff:
                emp.user_shift_windows[day].append((b2s, b2e_eff))

            # mapa de ShiftTypes compatibles con cada ventana del día
            for st in shift_types:
                ss = _t2m(st['start_time'])
                se = _t2m(st['end_time']) if st['end_time'] != time(0,0) else 24*60
                def fits(a, b): return ss <= _t2m(a) and _t2m(b) <= se
                if ((b1s and fits(b1s, b1e_eff)) or
                    (b2s and fits(b2s, b2e_eff))):
                    emp.user_shifts[day].add(st['id'])


        # 7) Leyes
        global MIN_HOURS_BETWEEN_SPLIT, MIN_HOURS_BETWEEN_SHIFTS, MAX_HOURS_PER_DAY
        min_hours_required = 0

        row = fetchall(cur, '''
            SELECT "CantHours" FROM "Management"."LawRestrictions"
            WHERE LOWER("Description") LIKE %s AND "CantHours" IS NOT NULL LIMIT 1
        ''', ('%horas minimo%',))
        if row:
            min_hours_required = int(row[0][0])
            if ASCII_LOGS: print(f"[LAW] Horas mínimas por semana: {min_hours_required}")

        row = fetchall(cur, '''
            SELECT "CantHours" FROM "Management"."LawRestrictions"
            WHERE LOWER("Description") LIKE %s AND "CantHours" IS NOT NULL LIMIT 1
        ''', ('%horas minimas entre bloques de turnos partidos%',))
        if row:
            try:
                MIN_HOURS_BETWEEN_SPLIT = int(row[0][0])
                if ASCII_LOGS: print(f"[LAW] Gap mínimo entre bloques (split): {MIN_HOURS_BETWEEN_SPLIT}h")
            except Exception:
                pass

        # 8) Cortes por bordes de UserShift
        extra_cuts_by_date = build_extra_cuts_from_usershifts_edges_only(emps_map, week)
        if ASCII_LOGS:
            dbg = {d.isoformat(): sorted(list(v))[:10] for d, v in extra_cuts_by_date.items()}
            print("[DEBUG] extra cuts (muestra):", dbg)

        demands = normalize_with_extra_cuts(demands, extra_cuts_by_date, max_hours=MAX_HOURS_PER_DAY)

        # 9) ShiftType por demanda + slot index
        for dm in demands:
            dm.shift_type = get_shifttype_for_demand(dm, shift_types)
        set_slot_indexes(demands)

        # DEBUG ejemplo
        for dm in demands:
            if dm.date.weekday() == 5 and dm.wsname == "CAMARERO BARRA":
                print(f"[DEBUG] DEM {dm.wsname} {dm.date} {dm.start.strftime('%H:%M')}-{dm.end.strftime('%H:%M')} need={dm.need}")

        if not demands: raise DataNotFoundError("La plantilla seleccionada no tiene demandas")

    return emps, demands, tpl_name, week, {}, shift_types, min_hours_required

# ───────── UserShift planner (enforce vs free) ─────────
def _minutes_candidate_in_usershift(emp: Emp, ddate: date, demands: List[Demand]) -> Tuple[int, str]:
    dow = ddate.weekday()
    if not emp.user_shift_windows.get(dow):
        return 0, "no_usershift_for_day"

    total = 0
    any_inside = False
    for dm in demands:
        if dm.date != ddate: continue
        if not (emp.can(dm.wsid) and emp.available(dm.date, dm.start, dm.end)): continue
        end = dm.end if dm.end != time(0,0) else time(23,59)
        in_any = False
        for w_s, w_e in emp.user_shift_windows[dow]:
            w_end = w_e if w_e != time(0,0) else time(23,59)
            if dm.start >= w_s and end <= w_end:
                in_any = True; break
        if not in_any: continue
        any_inside = True
        if hasattr(dm, 'shift_type') and dm.shift_type:
            if dm.shift_type['id'] not in emp.user_shifts.get(dow, set()):
                return 0, "shift_type_not_allowed"
        total += duration_min(dm)

    if not any_inside:
        return 0, "no_demands_inside_window"
    if total < MIN_SHIFT_DURATION_HOURS * 60:
        return total, "insufficient_volume_for_4h"
    return total, "ok"

def plan_usershift_day_modes(emps: List[Emp], demands: List[Demand], week: List[date]):
    overrides = set()
    plan = {}

    by_date = defaultdict(list)
    for dm in demands:
        by_date[dm.date].append(dm)

    for emp in emps:
        for d in week:
            ok, kind, reason = _usershift_day_eligibility(emp, d)
            if not ok:
                plan[(emp.id, d)] = {
                    "mode": "free_mode",
                    "reason": reason,
                    "kind": None,
                    "minutes_in_window": 0
                }
                overrides.add((emp.id, d))
                continue

            total_min, why = _minutes_candidate_in_usershift(emp, d, by_date.get(d, []))

            if total_min >= MIN_SHIFT_DURATION_HOURS * 60:
                plan[(emp.id, d)] = {
                    "mode": "usershift_enforced",
                    "reason": "ok",
                    "kind": kind,
                    "minutes_in_window": total_min
                }
            else:
                plan[(emp.id, d)] = {
                    "mode": "free_mode",
                    "reason": why,
                    "kind": None,
                    "minutes_in_window": total_min
                }
                overrides.add((emp.id, d))

    return overrides, plan

def add_usershift_must_cover_if_possible_with_overrides(mdl, emps, dem, X, overrides):
    if not HARD_REQUIRE_USERSHIFT:
        return

    # Index por fecha
    by_date = defaultdict(list)
    for d in dem:
        by_date[d.date].append(d)

    for e in emps:
        # Recorremos todos los días con demanda
        for day, day_dems in sorted(by_date.items(), key=lambda kv: kv[0]):
            if (e.id, day) in overrides:
                continue  # ese día no se fuerza

            dow = day.weekday()
            wins = sorted(e.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1])))
            if not wins:
                continue

            # Tomamos hasta 2 ventanas (estructura partido)
            taken = 0
            for (w_s, w_e) in wins:
                if taken >= 2:
                    break
                taken += 1

                w_end = w_e if w_e != time(0,0) else time(23,59)
                cands = []
                min_minutes_terms = []

                for dm in day_dems:
                    if (e.id, dm.id) not in X:
                        continue
                    end = dm.end if dm.end != time(0,0) else time(23,59)
                    if not (dm.start >= w_s and end <= w_end):
                        continue
                    if hasattr(dm, 'shift_type') and dm.shift_type:
                        if dm.shift_type['id'] not in e.user_shifts.get(dow, set()):
                            continue
                    cands.append(X[e.id, dm.id])
                    # minutos de este trozo (para la cota de ≥4h si se usa)
                    min_minutes_terms.append(duration_min(dm) * X[e.id, dm.id])

                if not cands:
                    # No hay candidatos en esta ventana: no la obligamos explícitamente.
                    continue

                # 1) Al menos 1 asignación dentro de la ventana
                mdl.Add(sum(cands) >= 1)

                # 2) Si se trabaja en la ventana, debe sumar ≥ 4h
                y_win = mdl.NewBoolVar(f"y_win_{e.id}_{day.isoformat()}_{_t2m(w_s)}_{_t2m(w_end)}")
                mdl.Add(sum(cands) >= y_win)
                mdl.Add(sum(cands) <= 1000 * y_win)
                mdl.Add(sum(min_minutes_terms) >= MIN_SHIFT_DURATION_HOURS * 60 * y_win)

# ───────── Utilidades solver (estricto/flexible) ─────────
def groups_without_usershift_candidates(emps: List[Emp], dem: List[Demand], overrides_emp_day: Set[Tuple[str, date]]):
    group_needs_relax = set()
    by_group = defaultdict(list)
    for d in dem: by_group[(d.date, d.wsid)].append(d)
    for (gdate, wsid), dlist in sorted(by_group.items(), key=lambda x: (x[0][0], str(x[0][1]))):
        found_any = False
        for emp in emps:
            for dm in dlist:
                if not (emp.can(dm.wsid) and emp.available(dm.date, dm.start, dm.end)): continue
                if (emp.id, gdate) in overrides_emp_day: found_any = True; break
                if emp.user_shift_windows.get(gdate.weekday()):
                    ok, _ = employee_can_work_demand_with_shifts(emp, dm, gdate.weekday())
                    if ok: found_any = True; break
                else:
                    found_any = True; break
            if found_any: break
        if not found_any:
            group_needs_relax.add((gdate, wsid))
            if ASCII_LOGS: print(f"[RELAX-GRUPO] (fecha={gdate}, wsid={wsid})")
    return group_needs_relax

def add_max2_blocks_per_day(mdl, emps, dem, X):
    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    for e in emps:
        for day in sorted(by_day.keys()):
            lst = sorted(by_day[day], key=lambda d: (_t2m(d.start), _t2m(d.end)))
            n = len(lst)
            for i in range(n):
                for j in range(i+1, n):
                    a,b = lst[i], lst[j]
                    if not (a.end <= b.start or b.end <= a.start): 
                        continue
                    for k in range(j+1, n):
                        c = lst[k]
                        if not (a.end <= c.start or c.end <= a.start): 
                            continue
                        if not (b.end <= c.start or c.end <= b.start): 
                            continue
                        if (e.id,a.id) in X and (e.id,b.id) in X and (e.id,c.id) in X:
                            mdl.Add(X[e.id,a.id] + X[e.id,b.id] + X[e.id,c.id] <= 2)

def build_consolidation_cost(mdl, emps, dem, X):
    groups = defaultdict(list)
    for d in dem:
        groups[(d.date, d.wsid)].append(d)
    y_vars = []
    for (gdate, wsid), dlist in sorted(groups.items(), key=lambda g: (g[0][0], str(g[0][1]))):
        for e in emps:
            relevant = [(e.id, d.id) in X for d in dlist]
            if not any(relevant): continue
            y = mdl.NewBoolVar(f"y_{e.id}_{gdate.isoformat()}_{wsid}")
            for d in dlist:
                if (e.id, d.id) in X:
                    mdl.AddImplication(X[e.id, d.id], y)
            y_vars.append(y)
    return sum(y_vars) if y_vars else 0

def build_usershift_window_penalty(mdl, emps, dem, X, overrides=set()):
    """
    Crea una suma de booleanos que valen 1 cuando asignamos (e,dm) FUERA de la ventana de UserShift
    teniendo ventanas ese día y sin override. El objetivo la minimizará ⇒ preferirá asignar dentro.
    """
    penalties = []
    for d in dem:
        for e in emps:
            key = (e.id, d.id)
            if key not in X:
                continue
            # si el empleado tiene ventana ese día y NO está en override
            if e.user_shift_windows.get(d.date.weekday(), []) and (e.id, d.date) not in overrides:
                end = d.end if d.end != time(0,0) else time(23,59)
                in_any = False
                for ws, we in e.user_shift_windows[d.date.weekday()]:
                    w_end = we if we != time(0,0) else time(23,59)
                    if d.start >= ws and end <= w_end:
                        # si la demanda tiene ST, debe ser compatible
                        if d.shift_type and d.shift_type['id'] not in e.user_shifts.get(d.date.weekday(), set()):
                            continue
                        in_any = True
                        break
                if not in_any:
                    # z = 1 si usamos este X fuera de ventana
                    z = mdl.NewBoolVar(f"pen_outside_us_{e.id}_{d.id}")
                    mdl.Add(z >= X[key])   # z >= x  ⇒ si x=1, z puede ser 1; objetivo hará el resto
                    penalties.append(z)
    # peso moderado: no debe romper cobertura, solo inclinar la balanza
    return (WEIGHT_USERWINDOW * sum(penalties)) if penalties else 0


def add_min_split_gap(mdl, emps, dem, X, min_gap_hours: int):
    # *** ELIMINADA del flujo: nos quedamos con la versión por ventanas de UserShift ***
    if True:
        return

def add_min_split_gap_usershift_windows(mdl, emps, dem, X, min_gap_hours: int):
    if not min_gap_hours or min_gap_hours <= 0: return
    min_gap_min = int(min_gap_hours * 60)
    by_date = defaultdict(list)
    for d in dem: by_date[d.date].append(d)

    def in_window(dm, ws, we):
        end = dm.end if dm.end != time(0,0) else time(23,59)
        return dm.start >= ws and end <= we

    for e in emps:
        for dow, wins in e.user_shift_windows.items():
            if not wins: continue
            wins_sorted = sorted(wins, key=lambda w: (_t2m(w[0]), _t2m(w[1])))
            for i in range(len(wins_sorted)):
                w1_s, w1_e = wins_sorted[i]
                w1_end = w1_e if w1_e != time(0,0) else time(23,59)
                w1_end_min = _t2m(w1_end)
                for j in range(i+1, len(wins_sorted)):
                    w2_s, w2_e = wins_sorted[j]
                    if not (w1_e <= w2_s): continue
                    gap = _t2m(w2_s) - w1_end_min
                    if not (0 < gap < min_gap_min): continue
                    for dday, day_dems in sorted(by_date.items(), key=lambda kv: kv[0]):
                        if dday.weekday() != dow: continue
                        A = [dm for dm in day_dems if in_window(dm, w1_s, w1_e)]
                        B = [dm for dm in day_dems if in_window(dm, w2_s, w2_e)]
                        for a in A:
                            for b in B:
                                if (e.id, a.id) in X and (e.id, b.id) in X:
                                    mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

def add_min_shift_duration_approx(mdl, emps, dem, X, min_hours_per_block: int):
    # *** SUSTITUIDA por add_min_per_contiguous_block. Se deja como no-op para claridad. ***
    return

def add_no_short_isolated_segments(mdl, emps, dem, X, min_hours_per_block: int):
    # *** SUSTITUIDA por add_min_per_contiguous_block. Se deja como no-op para claridad. ***
    return

def add_min_hours_per_day_per_workstation(mdl, emps, dem, X, min_hours: int):
    # *** ELIMINADA del flujo por apretar de más; dejamos la definición por compatibilidad. ***
    return

def add_min_per_contiguous_block(mdl, emps, dem, X, min_hours: int):
    """
    Requisito: si se activa cualquier segmento dentro de un bloque contiguo (por (día, ws, emp)),
    entonces la suma de ese bloque debe ser ≥ min_hours.
    Un bloque contiguo es una secuencia de segmentos [i..j] tal que start_{k+1} == end_k.
    """
    if not min_hours or min_hours <= 0: 
        return
    min_min = int(min_hours * 60)

    by_day_ws = defaultdict(list)
    for d in dem:
        by_day_ws[(d.date, d.wsid)].append(d)

    def tend(t: time) -> time:
        return t if t != time(0,0) else time(23,59)

    for e in emps:
        for (day, wsid), lst in by_day_ws.items():
            if wsid is None:
                continue
            lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(z.end)))
            n = len(lst)
            i = 0
            while i < n:
                j = i
                cur_end = _t2m(tend(lst[i].end))
                minutes_terms = []
                used_vars = []
                if (e.id, lst[i].id) in X:
                    minutes_terms.append(duration_min(lst[i]) * X[e.id, lst[i].id])
                    used_vars.append(X[e.id, lst[i].id])
                while j+1 < n and _t2m(lst[j+1].start) == cur_end:
                    j += 1
                    cur_end = _t2m(tend(lst[j].end))
                    if (e.id, lst[j].id) in X:
                        minutes_terms.append(duration_min(lst[j]) * X[e.id, lst[j].id])
                        used_vars.append(X[e.id, lst[j].id])

                if used_vars:
                    y_blk = mdl.NewBoolVar(f"blk_{e.id}_{day.isoformat()}_{wsid}_{i}_{j}")
                    mdl.Add(sum(used_vars) >= y_blk)
                    mdl.Add(sum(used_vars) <= 1000 * y_blk)
                    mdl.Add(sum(minutes_terms) >= min_min * y_blk)

                i = j + 1

def build_variables(mdl, emps, dem, overrides_emp_day, relax_groups):
    X = {}
    dem_sorted = sorted(dem, key=lambda d: (d.date, _t2m(d.start), _t2m(d.end), str(d.wsid)))
    for d in dem_sorted:
        for e in emps:
            if not (e.can(d.wsid) and e.available(d.date, d.start, d.end)):
                continue
            # si el grupo está relajado, permitimos fuera de ventana de usershift
            relax_this_group = (d.date, d.wsid) in relax_groups
            dow = d.date.weekday()
            end = d.end if d.end != time(0,0) else time(23,59)
            free_today = (e.id, d.date) in overrides_emp_day

            if not free_today and not relax_this_group and e.user_shift_windows.get(dow):
                in_window = False
                for w_s, w_e in sorted(e.user_shift_windows[dow], key=lambda w: (_t2m(w[0]), _t2m(w[1]))):
                    w_end = w_e if w_e != time(0,0) else time(23,59)
                    if d.start >= w_s and end <= w_end:
                        in_window = True; break
                if not in_window: 
                    continue
                if hasattr(d, 'shift_type') and d.shift_type:
                    if d.shift_type['id'] not in e.user_shifts.get(dow, set()):
                        continue
            X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if ASCII_LOGS: print(f"[VARS]  {{'comb': {len(emps)*len(dem)}, 'allow': {len(X)}}}")
    return X

def build_variables_with_usershift_logic(mdl, emps, dem, overrides: Set[Tuple[str, date]]):
    X = {}
    dem_sorted = sorted(dem, key=lambda d: (d.date, _t2m(d.start), _t2m(d.end), str(d.wsid)))
    for d in dem_sorted:
        for e in emps:
            if not (e.can(d.wsid) and e.available(d.date, d.start, d.end)):
                continue
            dow = d.date.weekday()
            end = d.end if d.end != time(0,0) else time(23,59)
            free_today = (e.id, d.date) in overrides
            if not free_today and e.user_shift_windows.get(dow):
                in_window = False
                for w_s, w_e in sorted(e.user_shift_windows[dow], key=lambda w: (_t2m(w[0]), _t2m(w[1]))):
                    w_end = w_e if w_e != time(0,0) else time(23,59)
                    if d.start >= w_s and end <= w_end: in_window = True; break
                if not in_window: continue
                if hasattr(d, 'shift_type') and d.shift_type:
                    if d.shift_type['id'] not in e.user_shifts.get(dow, set()):
                        continue
            X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if ASCII_LOGS: print(f"[VARS]  {{'comb': {len(emps)*len(dem)}, 'allow': {len(X)}}}")
    return X

# ───────── SOLVER ESTRICTO ─────────
def solve(emps: List[Emp], dem: List[Demand], week: List[date],
          overrides_emp_day: Set[Tuple[str, date]], min_hours_required: int = 0):
    relax_groups = groups_without_usershift_candidates(emps, dem, overrides_emp_day)
    mdl = cp_model.CpModel()
    X = build_variables(mdl, emps, dem, overrides_emp_day, relax_groups)
    if not X: raise ScheduleGenerationError("Sin variables: reglas dejan todo vacío.")

    for d in dem:
        mdl.Add(sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X) == d.need)

    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    for day in sorted(by_day.keys()):
        lst = sorted(by_day[day], key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    for e in emps:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                mdl.Add(sum(duration_min(dm) * X[e.id, dm.id] for dm in todays) <= MAX_HOURS_PER_DAY * 60)
        mdl.Add(sum(X[e.id, d.id] for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)
    
    if min_hours_required > 0:
        for e in emps:
            week_assignments = [dm for dm in dem if (e.id, dm.id) in X]
            if week_assignments:
                total_minutes_week = sum(duration_min(dm) * X[e.id, dm.id] for dm in week_assignments)
                mdl.Add(total_minutes_week >= min_hours_required * 60)

    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id,a.id) in X and (e.id,b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id,a.id] + X[e.id,b.id] <= 1)

    add_max2_blocks_per_day(mdl, emps, dem, X)
    # SOLO la restricción de gap mediante ventanas de usershift:
    add_min_split_gap_usershift_windows(mdl, emps, dem, X, MIN_HOURS_BETWEEN_SPLIT)
    # Requisito por BLOQUE contiguo ≥ 4h:
    add_min_per_contiguous_block(mdl, emps, dem, X, MIN_SHIFT_DURATION_HOURS)
    # Ya no llamamos: add_min_shift_duration_approx / add_no_short_isolated_segments / add_min_hours_per_day_per_workstation
    add_usershift_must_cover_if_possible(mdl, emps, dem, X)

    groups = defaultdict(list)
    for d in dem: groups[(d.date, d.wsid)].append(d)
    group_penalties = []
    for gk, dlist in sorted(groups.items(), key=lambda g: (g[0][0], str(g[0][1]))):
        gvar = mdl.NewBoolVar(f"grp_cover_{gk[0].isoformat()}_{gk[1]}")
        for d in dlist:
            for e in emps:
                if (e.id, d.id) in X:
                    mdl.AddImplication(X[e.id, d.id], gvar)
        group_penalties.append(1 - gvar)

    # consolidación (ya existente)
    consolidation_cost = build_consolidation_cost(mdl, emps, dem, X)
    usershift_penalty  = build_usershift_window_penalty(mdl, emps, dem, X, overrides_emp_day)
    mdl.Minimize(sum(group_penalties) * WEIGHT_MUST_HAVE_ONE + consolidation_cost + usershift_penalty)


    sol = cp_model.CpSolver()
    sol.parameters.random_seed = 0
    sol.parameters.num_search_workers = 1
    sol.parameters.max_time_in_seconds = 120
    st = sol.Solve(mdl)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE): raise ScheduleGenerationError("Modelo sin solución")

    out = defaultdict(list)
    for d in dem:
        for e in emps:
            if (e.id,d.id) in X and sol.Value(X[e.id,d.id]): out[d.date].append((e,d))
    return out, relax_groups

# ───────── SOLVER FLEXIBLE ─────────
def solve_flexible(emps: List[Emp], dem: List[Demand], week: List[date],
                   overrides: Set[Tuple[str,date]], min_hours_required: int = 0):
    mdl = cp_model.CpModel()
    X = build_variables_with_usershift_logic(mdl, emps, dem, overrides)
    if not X: raise ScheduleGenerationError("Sin variables viables tras reglas.")

    unmet = {d.id: mdl.NewIntVar(0, d.need, f"unmet_{d.id}") for d in dem}
    for d in dem:
        covered = sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X)
        mdl.Add(covered + unmet[d.id] == d.need)

    # No solapes por persona
    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    for day in sorted(by_day.keys()):
        lst = sorted(by_day[day], key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # Límite duro de horas por día y persona
    for e in emps:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                mdl.Add(sum(duration_min(dm) * X[e.id, dm.id] for dm in todays) <= MAX_HOURS_PER_DAY * 60)

    add_max2_blocks_per_day(mdl, emps, dem, X)
    # SOLO gap por ventanas
    add_min_split_gap_usershift_windows(mdl, emps, dem, X, MIN_HOURS_BETWEEN_SPLIT)
    # Requisito por BLOQUE contiguo ≥ 4h:
    add_min_per_contiguous_block(mdl, emps, dem, X, MIN_SHIFT_DURATION_HOURS)
    # No usamos: add_min_shift_duration_approx / add_no_short_isolated_segments / add_min_hours_per_day_per_workstation
    add_usershift_must_cover_if_possible_with_overrides(mdl, emps, dem, X, overrides)

    # Objetivo
    weights = {d.id: (WEIGHT_ULTRA_SLOT0 if d.slot_index==0 else (WEIGHT_SHORT_SLOT if duration_min(d)<=15 else 1000))
               for d in dem}
    total_unmet_weighted = sum(weights[d.id] * unmet[d.id] for d in dem)
    usershift_penalty    = build_usershift_window_penalty(mdl, emps, dem, X, overrides)
    mdl.Minimize(total_unmet_weighted + usershift_penalty)


    sol = cp_model.CpSolver()
    sol.parameters.random_seed = 0
    sol.parameters.num_search_workers = 1
    sol.parameters.max_time_in_seconds = 120
    status = sol.Solve(mdl)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        # Importante: NO lanzamos error. Devolvemos señal para aplicar fallback greedy.
        raise ScheduleGenerationError("CP-SAT flexible infactible — activar fallback greedy")

    out = defaultdict(list)
    coverage_stats = {}
    for d in dem:
        covered = sum(1 for e in emps if (e.id,d.id) in X and sol.Value(X[e.id,d.id]))
        u = sol.Value(unmet[d.id])
        coverage_stats[d.id] = {"demand": d, "covered": covered, "unmet": u,
                                "coverage_pct": round((covered/d.need)*100,1) if d.need>0 else 100}
        for e in emps:
            if (e.id,d.id) in X and sol.Value(X[e.id,d.id]): out[d.date].append((e,d))
    return out, coverage_stats

# ───────── GREEDY FALLBACK ─────────
def _fits_usershift_enforced(emp: Emp, dm: Demand) -> bool:
    dow = dm.date.weekday()
    end = dm.end if dm.end != time(0,0) else time(23,59)
    if not emp.user_shift_windows.get(dow): return False
    in_any = any(dm.start >= ws and end <= (we if we != time(0,0) else time(23,59))
                 for ws, we in emp.user_shift_windows[dow])
    if not in_any: return False
    if hasattr(dm, 'shift_type') and dm.shift_type:
        if dm.shift_type['id'] not in emp.user_shifts.get(dow, set()):
            return False
    return True

def _has_overlap(intervals: List[Tuple[int,int]], s: int, e: int) -> bool:
    for a,b in intervals:
        if not (e <= a or b <= s): return True
    return False
def _merge_sorted(intervals):
    if not intervals: return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s,e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def _respect_split_gap(merged, min_gap_hours: int):
    """merged: [(s,e)] minutos desde 00:00, ordenados y no solapados"""
    if not min_gap_hours or min_gap_hours <= 0: 
        return True
    min_gap = min_gap_hours * 60
    for i in range(len(merged) - 1):
        gap = merged[i+1][0] - merged[i][1]
        if 0 < gap < min_gap:
            return False
    return True

def _filter_blocks_min4_and_gap(assign_day_pairs, overrides, min_block_hours: int, min_gap_hours: int):
    """
    Recibe la lista de asignaciones de un día: [(emp, dm), ...]
    - Agrupa por (emp, wsid)
    - Dentro de cada grupo, fusiona en bloques contiguos y
      mantiene SOLO los bloques con duración >= min_block_hours.
    - Además exige que los gaps entre bloques cumplan min_gap_hours si el día NO está en override.
    Devuelve la nueva lista filtrada.
    """
    min_block = min_block_hours * 60
    by_emp_ws = defaultdict(list)  # (emp.id, wsid) -> [(s,e,emp,dm)]
    for emp, dm in assign_day_pairs:
        if dm.wsid is None:
            by_emp_ws[(emp.id, None)].append((0, 0, emp, dm))
            continue
        s = _t2m(dm.start)
        e = _t2m(dm.end if dm.end != time(0,0) else time(23,59))
        by_emp_ws[(emp.id, dm.wsid)].append((s, e, emp, dm))

    filtered = []

    for (eid, wsid), rows in by_emp_ws.items():
        if wsid is None:
            for _, _, emp, dm in rows:
                filtered.append((emp, dm))
            continue

        rows.sort(key=lambda r: (r[0], r[1]))
        merged_bounds = _merge_sorted([(s, e) for (s, e, _, _) in rows])

        any_dm = rows[0][3]
        day_override = (eid, any_dm.date) in overrides

        strong_blocks = [(s, e) for (s, e) in merged_bounds if (e - s) >= min_block]

        if not strong_blocks:
            continue

        if not day_override and not _respect_split_gap(strong_blocks, min_gap_hours):
            longest = max(strong_blocks, key=lambda b: (b[1]-b[0]))
            strong_blocks = [longest]

        for s, e in strong_blocks:
            for s0, e0, emp, dm in rows:
                if s0 >= s and e0 <= e:
                    filtered.append((emp, dm))

    return filtered


def greedy_fallback(emps: List[Emp], dem: List[Demand], week: List[date],
                    overrides: Set[Tuple[str,date]]):
    """
    Greedy con prioridad a empleados con UserShift el día (si no están en override).
    - Intenta formar cadenas contiguas ≥ 4h dentro de las ventanas/ShiftTypes válidos.
    - Si no logra cadena, asigna trozos sueltos y al final del día filtra bloques < 4h
      y gaps entre bloques < MIN_HOURS_BETWEEN_SPLIT (si el día no está en override).
    - Respeta límites de 9h/día, max 2 bloques/día por persona se gestiona indirectamente
      por el filtrado/gap y por las reglas que ya aplican después (CP o guardado).
    """
    assign = defaultdict(list)
    used_any = defaultdict(lambda: defaultdict(list))  # emp -> date -> [(s,e)]
    used_by_ws = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))  # emp -> date -> wsid -> [(s,e)]
    days_worked = defaultdict(set)

    # remanente por demanda
    remaining = {d.id: d.need for d in dem}

    # index (día, ws) -> lista de demandas ordenadas
    dem_sorted = sorted(dem, key=lambda d: (d.date, str(d.wsid), _t2m(d.start), _t2m(d.end if d.end != time(0,0) else time(23,59))))
    by_day_ws = defaultdict(list)
    for d in dem_sorted:
        by_day_ws[(d.date, d.wsid)].append(d)
    for k in by_day_ws:
        by_day_ws[k].sort(key=lambda d: (_t2m(d.start), _t2m(d.end if d.end != time(0,0) else time(23,59))))

    MIN_BLOCK_MIN = MIN_SHIFT_DURATION_HOURS * 60

    def has_overlap(ints, s, e):
        for a, b in ints:
            if not (e <= a or b <= s):
                return True
        return False

    def has_usershift_today(e: Emp, d: date) -> bool:
        """Tiene ventanas ese día y no está en override."""
        return bool(e.user_shift_windows.get(d.weekday(), [])) and ((e.id, d) not in overrides)

    def try_build_chain(emp: Emp, group: List[Demand], start_idx: int) -> List[Demand]:
        """
        Intenta armar una cadena contigua (cada seg. empieza donde termina el anterior)
        que alcance ≥ 4h, respetando:
          - disponibilidad 0–5 / excepciones,
          - roles,
          - ventanas de UserShift y ShiftType si NO está en override ese día,
          - no solape con lo ya usado en el día,
          - tope de 9h/día.
        """
        chosen = []
        dday = group[start_idx].date
        dow = dday.weekday()
        enforced = (emp.id, dday) not in overrides
        wins = sorted(emp.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1]))) if enforced else []
        tmp_used = list(used_any[emp.id][dday])  # copia para chequear solapes incrementales

        def fits_usershift(dm: Demand) -> bool:
            if not enforced:
                return True
            end = dm.end if dm.end != time(0,0) else time(23,59)
            for ws, we in wins:
                w_end = we if we != time(0,0) else time(23,59)
                if dm.start >= ws and end <= w_end:
                    # si hay ShiftType en la demanda, también debe ser compatible
                    if dm.shift_type and dm.shift_type['id'] not in emp.user_shifts.get(dow, set()):
                        return False
                    return True
            return False

        prev_end = None
        for k in range(start_idx, len(group)):
            dm = group[k]
            if remaining[dm.id] <= 0:
                continue
            if dm.date != dday or dm.wsid is None:
                continue
            if not (emp.can(dm.wsid) and emp.available(dm.date, dm.start, dm.end)):
                continue
            if enforced and not fits_usershift(dm):
                continue

            s = _t2m(dm.start)
            e = _t2m(dm.end if dm.end != time(0,0) else time(23,59))

            # contigüidad exacta
            if prev_end is not None and s != prev_end:
                break

            # no solape incremental con lo ya usado
            if has_overlap(tmp_used, s, e):
                break

            # tope de 9h/día
            total_today = sum((b - a) for a, b in tmp_used)
            if total_today + (e - s) > MAX_HOURS_PER_DAY * 60:
                break

            # pasa → añadimos provisionalmente
            chosen.append(dm)
            tmp_used.append((s, e))
            tmp_used.sort()

            # si ya alcanzamos 4h contiguas, paramos
            chain_len = (_t2m(chosen[-1].end if chosen[-1].end != time(0,0) else time(23,59))
                         - _t2m(chosen[0].start))
            if chain_len >= MIN_BLOCK_MIN:
                return chosen

            prev_end = e

        # no alcanzó 4h
        return []

    # ========= BUCLE PRINCIPAL =========
    for (day, wsid), group in by_day_ws.items():
        for idx, dm in enumerate(group):
            if remaining[dm.id] <= 0:
                continue

            # PRIORIDAD: primero quienes tienen UserShift ese día (y no override), luego por nombre
            emps_ordered = sorted(
                emps,
                key=lambda ee: (0 if has_usershift_today(ee, day) else 1, ee.name)
            )

            for emp in emps_ordered:
                if remaining[dm.id] <= 0:
                    break
                if len(days_worked[emp.id]) >= MAX_DAYS_PER_WEEK and day not in days_worked[emp.id]:
                    continue
                if not (emp.can(dm.wsid) and emp.available(dm.date, dm.start, dm.end)):
                    continue

                # 1) intentar CADENA contigua ≥ 4h empezando en este trozo
                chain = try_build_chain(emp, group, idx)
                if chain:
                    # commit de la cadena
                    for dmx in chain:
                        if remaining[dmx.id] <= 0:
                            continue
                        ss = _t2m(dmx.start)
                        ee = _t2m(dmx.end if dmx.end != time(0,0) else time(23,59))
                        assign[day].append((emp, dmx))
                        used_any[emp.id][day].append((ss, ee))
                        used_any[emp.id][day].sort()
                        used_by_ws[emp.id][day][dmx.wsid] = merge_intervals(
                            used_by_ws[emp.id][day][dmx.wsid] + [(ss, ee)]
                        )
                        days_worked[emp.id].add(day)
                        remaining[dmx.id] -= 1
                    continue  # siguiente demanda

                # 2) si no hay cadena, intentar el trozo suelto (validamos al cierre del día)
                ss = _t2m(dm.start)
                ee = _t2m(dm.end if dm.end != time(0,0) else time(23,59))

                # no solape con lo ya asignado
                if has_overlap(used_any[emp.id][day], ss, ee):
                    continue

                # límite 9h/día
                total_today = sum((b - a) for a, b in used_any[emp.id][day])
                if total_today + (ee - ss) > MAX_HOURS_PER_DAY * 60:
                    continue

                # si el día está "enforced" por UserShift, el trozo debe caer dentro
                enforced = (emp.id, day) not in overrides
                if enforced and not _fits_usershift_enforced(emp, dm):
                    continue

                # commit del trozo suelto
                assign[day].append((emp, dm))
                used_any[emp.id][day].append((ss, ee))
                used_any[emp.id][day].sort()
                used_by_ws[emp.id][day][dm.wsid] = merge_intervals(
                    used_by_ws[emp.id][day][dm.wsid] + [(ss, ee)]
                )
                days_worked[emp.id].add(day)
                remaining[dm.id] -= 1

    # ========= POST-PROCESO: filtrar bloques < 4h y gaps inválidos =========
    for day in list(assign.keys()):
        filtered = _filter_blocks_min4_and_gap(
            assign[day],
            overrides,
            MIN_SHIFT_DURATION_HOURS,
            MIN_HOURS_BETWEEN_SPLIT
        )
        assign[day] = filtered

    # ========= Estadísticas =========
    coverage_stats = {}
    for dm in dem:
        covered = sum(1 for emp, d2 in assign[dm.date] if d2.id == dm.id)
        coverage_stats[dm.id] = {
            "demand": dm,
            "covered": covered,
            "unmet": max(0, dm.need - covered),
            "coverage_pct": round(covered / dm.need * 100, 1) if dm.need else 100
        }

    return assign, coverage_stats

# ───────── OBS / GENERATE ─────────
def merge_intervals(intervals):
    if not intervals: return []
    intervals.sort(); merged = [intervals[0]]
    for s,e in intervals[1:]:
        ls,le = merged[-1]
        if s <= le: merged[-1] = (ls, max(le,e))
        else: merged.append((s,e))
    return merged

def _can_place_in_bucket(emp, ddate, wsid, used_intervals, bucket_intervals, seg_s, seg_e):
    """
    Verifica no solape con lo ya asignado del empleado ese día (used_intervals)
    y con lo que lleva tentativamente en el bucket de este ws (bucket_intervals).
    """
    # no solape con asignaciones confirmadas del día
    for a, b in used_intervals.get(emp.id, {}).get(ddate, []):
        if not (seg_e <= a or b <= seg_s):
            return False
    # no solape dentro del bucket
    for a, b in bucket_intervals.get((emp.id, ddate, wsid), []):
        if not (seg_e <= a or b <= seg_s):
            return False
    return True

def _bucket_minutes_after_merge(bucket_intervals, key, seg_s, seg_e):
    """
    Simula añadir [seg_s, seg_e) al bucket 'key' y devuelve la
    duración total coalescida en minutos del bucket resultante.
    """
    ivs = bucket_intervals.get(key, []) + [(seg_s, seg_e)]
    ivs.sort()
    merged = []
    for s, e in ivs:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)
    return sum(b - a for a, b in merged), [(a, b) for a, b in merged]

def calc_obs(emp: Emp, dm: Demand, assigns_day: list, fixed_ids: set):
    if (emp.id, dm.id) in fixed_ids: return ""
    same_ws = [d for e2, d in assigns_day if d.wsid == dm.wsid and d.date == dm.date and d.wsid is not None]
    if not same_ws: return "BT"
    latest_end = max(d.end if d.end != time(0,0) else time(23,59) for d in same_ws)
    current_end = dm.end if dm.end != time(0,0) else time(23,59)
    return "C" if current_end == latest_end else "BT"

def build_usershift_reports(emps, week, usershift_plan, sched):
    def _covered_inside_window(emp: Emp, day: date) -> bool:
        wins = emp.user_shift_windows.get(day.weekday(), [])
        if not wins:
            return False
        # normalizar ventanas a minutos
        win_min = []
        for ws, we in wins:
            s = _t2m(ws)
            e = _t2m(we if we != time(0,0) else time(23,59))
            win_min.append((s, e))

        for e2, dm in sched.get(day, []):
            if e2.id != emp.id or dm.wsid is None:
                continue
            s = _t2m(dm.start)
            e = _t2m(dm.end if dm.end != time(0,0) else time(23,59))
            # ¿Está completamente dentro de alguna ventana?
            for a, b in win_min:
                if s >= a and e <= b:
                    return True
        return False

    usershift_assignment_report = []
    usershift_windows_report = []

    for emp in emps:
        for d in week:
            entry  = usershift_plan.get((emp.id, d), {"mode":"free_mode","reason":"no_usershift_for_day","minutes_in_window":0, "kind":None})
            mode   = entry.get("mode", "free_mode")
            reason = entry.get("reason", "no_usershift_for_day")
            mins   = entry.get("minutes_in_window", 0)
            kind   = entry.get("kind", None)

            # Estado de cobertura del UserShift (no del día entero)
            covered_inside = _covered_inside_window(emp, d)
            usershift_status = "assigned_inside" if covered_inside else "not_assigned"

            usershift_assignment_report.append({
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "date": d.isoformat(),
                "mode": mode,                        # usershift_enforced | free_mode
                "kind": kind,                        # single | split | None
                "usershift_status": usershift_status, # assigned_inside | not_assigned
                "reason": reason,                    # por qué pasó a libre o por qué no se cubrió
                "minutes_in_window": mins
            })

            if reason != "ok":
                usershift_windows_report.append({
                    "date": d.isoformat(),
                    "employee_id": str(emp.id),
                    "employee_name": emp.name,
                    "reason": reason
                })

    return usershift_assignment_report, usershift_windows_report

def generate(week_start: date):
    emps, demands, tpl, week, fixed, shift_types, min_hours_required = load_data(week_start)
    overrides, usershift_plan = plan_usershift_day_modes(emps, demands, week)
    sched, relaxed_groups = solve(emps, demands, week, overrides, min_hours_required)

    for d, lst in fixed.items(): sched[d].extend(lst)
    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {"id": uid(), "wsid": None, "wsname": "AUSENCIA",
                                                "start": time(0,0), "end": time(0,0), "date": d})()
                sched[d].append((emp, pseudo_dm))

    usershift_assignment_report, usershift_windows_report = build_usershift_reports(emps, week, usershift_plan, sched)

    total_req = sum(dm.need for dm in demands) + len(fixed_ids)
    total_ass = sum(len(v) for v in sched.values())

    overrides_list = [{"employee_id": str(eid),
                       "employee_name": next((e.name for e in emps if e.id == eid), ""),
                       "date": d.isoformat()} for (eid, d), v in usershift_plan.items() if v["mode"] == "free_mode"]

    relaxed_list = [{"date": gdate.isoformat(), "workstation_id": str(wsid)}
                    for (gdate, wsid) in sorted(relaxed_groups, key=lambda x: (x[0], str(x[1])))]

    res = {
        "template": tpl,
        "week_start": week_start.isoformat(),
        "week_end":   (week_start + timedelta(days=6)).isoformat(),
        "summary": {
            "total_employees": len(emps),
            "total_demands":   total_req,
            "total_assignments": total_ass,
            "coverage": round(total_ass/total_req*100, 1) if total_req else 0,
            "flexible_mode": False,
            "usershift_free_overrides": overrides_list,
            "relaxed_groups_for_must_have_one": relaxed_list,
            "usershift_assignment_report": usershift_assignment_report,
            "usershift_windows_report": usershift_windows_report
        },
        "schedule": {}
    }
    for d in week:
        k = d.isoformat(); res["schedule"][k] = []
        for emp, dm in sorted(sched.get(d, []), key=lambda x: (x[0].name, x[1].wsname, _t2m(x[1].start))):
            res["schedule"][k].append({
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "workstation_id": (str(dm.wsid) if dm.wsid is not None else None),
                "workstation_name": dm.wsname,
                "start_time": (dm.start.strftime("%H:%M") if dm.start else None),
                "end_time": (dm.end.strftime("%H:%M") if dm.end else None),
                "observation": ("VAC" if dm.wsid is None and emp.abs_reason.get(d) == "VAC"
                                else "ABS" if dm.wsid is None
                                else calc_obs(emp, dm, sched[d], fixed_ids))
            })
    return res, sched, emps, week, fixed_ids

def generate_flexible(week_start: date):
    emps, demands, tpl, week, fixed, shift_types, min_hours_required = load_data(week_start)
    overrides, usershift_plan = plan_usershift_day_modes(emps, demands, week)

    # 1) Intento CP-SAT flexible
    try:
        sched, coverage_stats = solve_flexible(emps, demands, week, overrides, min_hours_required)
        solved_by = "cp_sat"
    except ScheduleGenerationError:
        # 2) Fallback GREEDY
        sched, coverage_stats = greedy_fallback(emps, demands, week, overrides)
        solved_by = "greedy_fallback"

    # Ausencias
    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {"id": uid(), "wsid": None, "wsname": "AUSENCIA",
                                                "start": time(0,0), "end": time(0,0), "date": d})()
                sched[d].append((emp, pseudo_dm))

    usershift_assignment_report, usershift_windows_report = build_usershift_reports(emps, week, usershift_plan, sched)

    total_req = sum(dm.need for dm in demands)
    total_cov = sum(s["covered"] for s in coverage_stats.values())
    total_unmet = sum(s["unmet"] for s in coverage_stats.values())

    overrides_list = [{"employee_id": str(eid),
                       "employee_name": next((e.name for e in emps if e.id == eid), ""),
                       "date": d.isoformat()} for (eid, d), v in usershift_plan.items() if v["mode"] == "free_mode"]

    res = {
        "template": tpl,
        "week_start": week_start.isoformat(),
        "week_end": (week_start + timedelta(days=6)).isoformat(),
        "summary": {
            "total_employees": len(emps),
            "total_demands": total_req,
            "total_covered": total_cov,
            "total_unmet": total_unmet,
            "coverage": round((total_cov / total_req) * 100, 1) if total_req else 100,
            "flexible_mode": True,
            "solver": solved_by,
            "usershift_free_overrides": overrides_list,
            "usershift_assignment_report": usershift_assignment_report,
            "usershift_windows_report": usershift_windows_report
        },
        "coverage_details": {
            d_id: {
                "workstation": s["demand"].wsname,
                "date": s["demand"].date.isoformat(),
                "time": f"{s['demand'].start.strftime('%H:%M')}-{s['demand'].end.strftime('%H:%M')}",
                "demanded": s["demand"].need,
                "covered": s["covered"],
                "unmet": s["unmet"],
                "coverage_pct": s["coverage_pct"]
            } for d_id, s in coverage_stats.items()
        },
        "schedule": {}
    }
    for d in week:
        k = d.isoformat(); res["schedule"][k] = []
        for emp, dm in sorted(sched.get(d, []), key=lambda x: (x[0].name, x[1].wsname, _t2m(x[1].start))):
            res["schedule"][k].append({
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "workstation_id": (str(dm.wsid) if dm.wsid is not None else None),
                "workstation_name": dm.wsname,
                "start_time": (dm.start.strftime("%H:%M") if dm.start else None),
                "end_time": (dm.end.strftime("%H:%M") if dm.end else None),
                "observation": ("VAC" if dm.wsid is None and emp.abs_reason.get(d) == "VAC"
                                else "ABS" if dm.wsid is None
                                else "BT")
            })
    return res, sched, emps, week, set()

# ───────── Coalesce para guardar ─────────
def coalesce_employee_day_workstation(assigns_day):
    by_key = defaultdict(list)
    for emp, dm in assigns_day:
        if dm.wsid is None:
            by_key[(emp.id, None)].append((emp, _t2m(dm.start), _t2m(dm.end if dm.end != time(0,0) else time(23,59)), [dm]))
            continue
        s = _t2m(dm.start)
        e = _t2m(dm.end if dm.end != time(0,0) else time(23,59))
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

# ───────── ENDPOINTS ─────────
@app.route('/api/health')
def health():
    st = {"status":"checking","timestamp":now().isoformat(),"version":"3.14","checks":{}}
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute("SELECT version()")
            st["checks"]["database"] = {"status":"healthy","version":cur.fetchone()[0].split(',')[0]}
            st["status"] = "healthy"
    except Exception as e:
        st["checks"]["database"] = {"status":"unhealthy","message":str(e)}
        st["status"] = "unhealthy"
    return jsonify(st), (200 if st["status"]=="healthy" else 503)

@app.route('/api/agenda/preview')
def preview():
    wk = request.args.get('week_start')
    flexible = request.args.get('flexible', 'true').lower() == 'true'
    if not wk: return jsonify({"error":"Falta week_start"}), 400
    try: ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError: return jsonify({"error":"Fecha inválida"}), 400
    try:
        if flexible:
            res, _, _, _, _ = generate_flexible(ws)
        else:
            res, _, _, _, _ = generate(ws)
        return jsonify(res), 200
    except (DatabaseConnectionError, DataNotFoundError) as e:
        return jsonify({"error": str(e)}), 400

@app.route('/api/agenda/save', methods=['POST'])
def save():
    data = request.get_json() or {}
    wk = data.get('week_start')
    force = data.get('force', False)
    flexible = data.get('flexible', True)
    if not wk: return jsonify({"error":"Falta week_start"}), 400
    try: ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError: return jsonify({"error":"Fecha inválida"}), 400
    we = ws + timedelta(days=6)

    try:
        res, sched, emps, week, fixed_ids = (generate_flexible(ws) if flexible else generate(ws))
    except (DatabaseConnectionError, DataNotFoundError) as e:
        return jsonify({"error": str(e)}), 400

    # Inserción determinista (coalescida) con calc_obs
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute('SELECT COUNT(*) FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s', (ws, we))
            if cur.fetchone()[0] and not force:
                return jsonify({"error": "Horario ya existe para esa semana"}), 409
            if force:
                cur.execute('DELETE FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s', (ws, we))

            for d in sorted(sched.keys()):
                ass = sorted(sched[d], key=lambda x: (x[0].name, x[1].wsname, _t2m(x[1].start)))

                # Ausencias
                for emp, dm in ass:
                    if dm.wsid is None:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId","StartTime","EndTime","Observation","IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (uid(), d, str(emp.id), None, None, None, emp.abs_reason.get(d,'ABS'), False, now()))

                # Coalesce + obs
                coalesced = coalesce_employee_day_workstation(ass)

                latest_end_by_wsid = {}
                for _, dm in ass:
                    if dm.wsid is None: continue
                    end_t = dm.end if dm.end != time(0,0) else time(23,59)
                    latest_end_by_wsid[dm.wsid] = max(latest_end_by_wsid.get(dm.wsid, time(0,0)), end_t)

                for (eid, wsid), rows in coalesced.items():
                    if wsid is None:
                        continue
                    for emp, s_min, e_min, src_dms in rows:
                        s_t = _m2t(s_min)
                        e_t = _m2t(e_min if e_min < 24*60 else 0)

                        dur_min = e_min - s_min               # s_min / e_min ya están en MINUTOS
                        if dur_min < MIN_SHIFT_DURATION_HOURS * 60:
                            if ASCII_LOGS:
                                print(f"[SAVE-GUARD] Bloque <{MIN_SHIFT_DURATION_HOURS}h no insertado: "
                                    f"user={emp.name}, fecha={d}, wsid={wsid}, {s_t.strftime('%H:%M')}-{e_t.strftime('%H:%M')}")
                            continue

                        has_fixed = any((emp.id, dm.id) in fixed_ids for dm in src_dms)
                        if has_fixed:
                            obs = ""
                        else:
                            latest_end = latest_end_by_wsid.get(wsid, None)
                            obs = "C" if latest_end and e_t == (latest_end if latest_end != time(0,0) else time(23,59)) else "BT"

                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId","StartTime","EndTime","Observation","IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (
                            uid(), d, str(emp.id), str(wsid),
                            timedelta(hours=s_t.hour, minutes=s_t.minute),
                            timedelta(hours=e_t.hour,   minutes=e_t.minute),
                            obs, False, now()
                        ))
            c.commit()
    except Exception as e:
        return jsonify({"error": "Error al guardar", "detail": str(e)}), 500

    return jsonify({"message": ("Horario guardado (flexible)" if flexible else "Horario guardado"), **res}), 201

# ───────── MAIN ─────────
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
if __name__ == "__main__":
    print("API Gandarias v3.14 en http://localhost:5000")
    print("Modo flexible nunca responde 'sin solución': usa fallback greedy si hace falta.")
    app.run(host="0.0.0.0", port=5000, debug=True)
