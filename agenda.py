#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGENDA GENERATOR API – Gandarías v3.13
• Primero intentamos garantizar 1 persona por (día, puesto) (relaja UserShift por grupo si hace falta).
• UserShifts obligatorios si hay match; si NO hay match por empleado/día ⇒ asignación libre (cumpliendo 0–5).
• 0–5 SIEMPRE (día libre, ventanas, excepciones, ausencias).
• NUEVO v3.13: se PARTEN DEMANDAS en los BORDES de cada UserShift. Ej.: 12–14 ⇒ 12–13 y 13–14.
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
MIN_HOURS_BETWEEN_SPLIT = 4
MAX_DAYS_PER_WEEK = 6
MAX_HOURS_PER_DAY = 9
MAX_SHIFT_DURATION_HOURS = 9

# Pesos
WEIGHT_MUST_HAVE_ONE = 200_000
WEIGHT_ULTRA_SLOT0   = 500_000
WEIGHT_SHORT_SLOT    = 100_000

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

# ───────── DB helpers ─────────
def conn():
    try:
        return psycopg2.connect(**DB)
    except OperationalError as e:
        t = str(e)
        if "could not connect" in t: raise DatabaseConnectionError("No se puede conectar al servidor de BD")
        if "authentication failed" in t: raise DatabaseConnectionError("Credenciales de BD incorrectas")
        raise DatabaseConnectionError(t)

def fetchall(cur, sql, pars=()):
    try:
        cur.execute(sql, pars); return cur.fetchall()
    except (ProgrammingError, DataError) as e:
        raise DataIntegrityError(str(e))

def monday(d: date) -> date:
    while d.weekday() != 0: d -= timedelta(days=1)
    return d

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
                and pot_dur_h <= MAX_SHIFT_DURATION_HOURS):
                curr.end = nxt.end
            else:
                merged.append(curr); curr = nxt
        merged.append(curr)
    out = [Demand((d.id, d.date, d.wsid, d.wsname, d.start, d.end, d.need)) for d in merged]
    return out

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
            if (b - a) <= MAX_SHIFT_DURATION_HOURS * 60:
                out.append(Demand((uid(), dte, wsid, wsname, _m2t(a), _m2t(b if b < 24*60 else 0), n)))
            else:
                out.extend(split_long_segment(dte, wsid, wsname, a, b, n, MAX_SHIFT_DURATION_HOURS))
        if over_sum_detected and PEAK_CAP_LOG:
            print(f"[NORMALIZACION] {dte} {wsname}: solapes reducidos usando MAX(need).")
    return out

def set_slot_indexes(demands):
    by_day_ws = defaultdict(list)
    for d in demands: by_day_ws[(d.date, d.wsid)].append(d)
    for (_, _), lst in by_day_ws.items():
        lst.sort(key=lambda x: (_t2m(x.start), _t2m(x.end)))
        for idx, d in enumerate(lst): d.slot_index = idx

# ───────── NUEVO: Cortes sólo en BORDES de UserShifts ─────────
def build_extra_cuts_from_usershifts_edges_only(emps: Dict[str, Emp], week: List[date]):
    """
    {date -> set(minutos)} con cortes en los BORDES (start/end) de cada ventana UserShift.
    Así, si existe demanda 12–14 y ventana 13–14, tendremos cortes 13:00 y 14:00,
    y la normalización creará 12–13 y 13–14 (bloque único exacto dentro del UserShift).
    """
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

def normalize_with_extra_cuts(demands: List[Demand],
                              extra_cuts_by_date: Dict[date, Set[int]],
                              max_hours: int = MAX_SHIFT_DURATION_HOURS,
                              peak_cap: bool = ENFORCE_PEAK_CAP,
                              log_cap: bool = PEAK_CAP_LOG):
    """
    Parte cada demanda por los cortes de extra_cuts_by_date[fecha] que caigan dentro del intervalo.
    Luego respeta el límite de horas por segmento (split_long_segment).
    """
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

# ───────── SHIFTTYPES ─────────
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
    ''')
    if not rows: raise DataNotFoundError("No existen plantillas con StartDate/EndDate")

    def md(x: date): return (x.month, x.day)
    def same_year(year: int, m: int, d: int) -> date:
        try: return date(year, m, d)
        except ValueError: return date(year, 2, 28) if (m == 2 and d == 29) else date(year, m, d)

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

# ───────── CARGA DATOS (ORDEN CORRECTO) ─────────
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
        # 1) Plantilla y demandas crudas
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
            ORDER BY d."Day", d."StartTime"
        ''', (week_start, tpl_id))]
        # (opcional) fusionar pequeños huecos
        demands = coalesce_demands(demands, tolerate_gap_min=0)
        # cap de picos por MAX(need) antes de cortes de UserShift
        demands = normalize_by_max_need_profile(demands)

        # 2) Empleados + roles
        emps = {r[0]: Emp(r) for r in fetchall(cur, '''
            SELECT "Id", COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                   COALESCE("ComplementHours", TRUE)
            FROM "Management"."AspNetUsers"
            WHERE "IsActive" AND NOT "IsDelete"
        ''')}
        if not emps: raise DataNotFoundError("No hay empleados activos")

        for uid, ws in fetchall(cur, '''
            SELECT "UserId","WorkstationId"
            FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete"
        '''):
            if uid in emps: emps[uid].roles.add(ws)
        if not any(e.roles for e in emps.values()): raise DataNotFoundError("Ningún empleado tiene roles asignados")

        # 3) Restricciones semanales (0–5)
        for uid, dow, rt, f1, t1, b1s, b1e, b2s, b2e in fetchall(cur, '''
            SELECT "UserId","DayOfWeek","RestrictionType",
                   "AvailableFrom","AvailableUntil",
                   "Block1Start","Block1End",
                   "Block2Start","Block2End"
            FROM "Management"."EmployeeScheduleRestrictions"
        '''):
            if uid not in emps: continue
            emp = emps[uid]
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
        for uid, d, rt, f, t in fetchall(cur, '''
            SELECT "UserId","Date","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s
        ''', (week_start, week_end)):
            if uid not in emps: continue
            emp = emps[uid]
            if rt == 0: emp.absent.add(d)
            else:
                s = _to_time(f); e = _to_time(t)
                if s and e and s < e:
                    if e == time(0,0): e = time(23,59)
                    emp.exc[d].append((s, e))

        for uid, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
            FROM "Management"."Licenses"
            WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
        ''', (week_end, week_end, week_end, week_start)):
            if uid not in emps: continue
            emp = emps[uid]; d = max(sd, week_start)
            while d <= ed:
                emp.absent.add(d); emp.abs_reason[d] = 'VAC'; d += timedelta(days=1)

        for uid, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
            FROM "Management"."UserAbsenteeisms"
            WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
        ''', (week_end, week_end, week_end, week_start)):
            if uid not in emps: continue
            emp = emps[uid]; d = max(sd, week_start)
            while d <= ed:
                emp.absent.add(d); emp.abs_reason[d] = 'ABS'; d += timedelta(days=1)

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
        '''):
            shift_types.append({
                'id': row[0], 'name': row[1], 'description': row[2],
                'start_time': row[3], 'end_time': row[4], 'is_split': row[5], 'is_active': row[6]
            })

        # 6) UserShifts (ventanas + ST compatibles)
        for uid, day, structure, b1s, b1e, b2s, b2e in fetchall(cur, '''
            SELECT "UserId","Day","Structure",
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time,
                   (TIMESTAMP '2000-01-01' + "Block2Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block2lastStart")::time
            FROM "Management"."UserShifts"
        '''):
            if uid not in emps: continue
            emp = emps[uid]
            if b1s and b1e and b1s < b1e: emp.user_shift_windows[day].append((b1s, b1e))
            if b2s and b2e and b2s < b2e: emp.user_shift_windows[day].append((b2s, b2e))
            for st in shift_types:
                ss = _t2m(st['start_time']); se = _t2m(st['end_time']) if st['end_time'] != time(0,0) else 24*60
                def fits(a,b): return ss <= _t2m(a) and _t2m(b) <= se
                if (b1s and b1e and fits(b1s,b1e)) or (b2s and b2e and fits(b2s,b2e)):
                    emp.user_shifts[day].add(st['id'])

        # 7) Cortes por BORDES de UserShift y normalización con cortes
        extra_cuts_by_date = build_extra_cuts_from_usershifts_edges_only(emps, week)
        if ASCII_LOGS:
            # para depurar: imprime algunos días con cortes
            dbg = {d.isoformat(): sorted(list(v))[:10] for d, v in extra_cuts_by_date.items()}
            print("[DEBUG] extra cuts (muestra):", dbg)

        demands = normalize_with_extra_cuts(
            demands,
            extra_cuts_by_date,
            max_hours=MAX_SHIFT_DURATION_HOURS,
            peak_cap=ENFORCE_PEAK_CAP,
            log_cap=PEAK_CAP_LOG
        )

        # 8) Vincular demandas con ShiftTypes y slot index
        for dm in demands:
            dm.shift_type = get_shifttype_for_demand(dm, shift_types)
        set_slot_indexes(demands)

        # DEBUG sábado – debe existir CAMARERO BARRA 13:00–14:00
        for dm in demands:
            if dm.date.weekday() == 5 and dm.wsname == "CAMARERO BARRA":
                print(f"[DEBUG] DEM {dm.wsname} {dm.date} {dm.start.strftime('%H:%M')}-{dm.end.strftime('%H:%M')} need={dm.need}")

        if not demands: raise DataNotFoundError("La plantilla seleccionada no tiene demandas")

    return list(emps.values()), demands, tpl_name, week, {}, shift_types

# ───────── UserShift: overrides por empleado/día ─────────
def usershift_day_has_any_match(emp: Emp, ddate: date, demands: List[Demand]) -> bool:
    dow = ddate.weekday()
    if not emp.user_shift_windows.get(dow): return True
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
        if hasattr(dm, 'shift_type') and dm.shift_type:
            if dm.shift_type['id'] not in emp.user_shifts.get(dow, set()):
                continue
        return True
    return False

def compute_usershift_free_overrides(emps: List[Emp], demands: List[Demand], week: List[date]):
    overrides = set()
    for emp in emps:
        for d in week:
            if emp.user_shift_windows.get(d.weekday()):
                if not usershift_day_has_any_match(emp, d, demands):
                    overrides.add((emp.id, d))
                    if ASCII_LOGS: print(f"[UserShift→LIBRE] {emp.name} {d}")
    return overrides

# ───────── Prioridad grupo (día, puesto) ─────────
def groups_without_usershift_candidates(emps: List[Emp], dem: List[Demand], overrides_emp_day: Set[Tuple[str, date]]):
    group_needs_relax = set()
    by_group = defaultdict(list)
    for d in dem: by_group[(d.date, d.wsid)].append(d)
    for (gdate, wsid), dlist in by_group.items():
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

# ───────── Aux: máx 2 bloques/día ─────────
def add_max2_blocks_per_day(mdl, emps, dem, X):
    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    def disjoint(a,b): return (a.end <= b.start) or (b.end <= a.start)
    for e in emps:
        for day, lst in by_day.items():
            lst_sorted = sorted(lst, key=lambda d: (d.start, d.end))
            n = len(lst_sorted)
            for i in range(n):
                for j in range(i+1, n):
                    a,b = lst_sorted[i], lst_sorted[j]
                    if not disjoint(a,b): continue
                    for k in range(j+1, n):
                        c = lst_sorted[k]
                        if not disjoint(b,c) or not disjoint(a,c): continue
                        if (e.id,a.id) in X and (e.id,b.id) in X and (e.id,c.id) in X:
                            mdl.Add(X[e.id,a.id] + X[e.id,b.id] + X[e.id,c.id] <= 2)

# ───────── Variables (con UserShift y relax) ─────────
def build_variables(mdl, emps, dem, overrides_emp_day: Set[Tuple[str, date]], relax_groups: Set[Tuple[date, str]]):
    X = {}
    stats = defaultdict(int)
    for d in dem:
        gkey = (d.date, d.wsid)
        dow = d.date.weekday()
        for e in emps:
            stats['comb'] += 1
            if not (e.can(d.wsid) and e.available(d.date, d.start, d.end)):
                stats['block_0_5'] += 1; continue
            free_today = (e.id, d.date) in overrides_emp_day
            relax_group = gkey in relax_groups
            if free_today or relax_group or not e.user_shift_windows.get(dow):
                stats['allow_free'] += 1
                X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
                continue
            ok, why = employee_can_work_demand_with_shifts(e, d, dow)
            if not ok:
                stats[f'block_{why}'] += 1; continue
            stats['allow_usershift'] += 1
            X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if ASCII_LOGS: print(f"[VARS] {dict(stats)}")
    return X

def build_variables_with_usershift_logic(mdl, emps, dem, overrides: Set[Tuple[str, date]]):
    X = {}
    stats = defaultdict(int)
    for d in dem:
        for e in emps:
            stats['comb'] += 1
            if not (e.can(d.wsid) and e.available(d.date, d.start, d.end)):
                stats['block_0_5'] += 1; continue
            dow = d.date.weekday()
            end = d.end if d.end != time(0,0) else time(23,59)
            free_today = (e.id, d.date) in overrides
            if not free_today and e.user_shift_windows.get(dow):
                in_window = False
                for w_s, w_e in e.user_shift_windows[dow]:
                    w_end = w_e if w_e != time(0,0) else time(23,59)
                    if d.start >= w_s and end <= w_end: in_window = True; break
                if not in_window: stats['block_outside_window'] += 1; continue
                if hasattr(d, 'shift_type') and d.shift_type:
                    if d.shift_type['id'] not in e.user_shifts.get(dow, set()):
                        stats['block_st'] += 1; continue
                stats['allow_usershift'] += 1
            else:
                stats['allow_free'] += 1
            X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if ASCII_LOGS: print("[VARS] ", dict(stats))
    return X

# ───────── SOLVER ESTRICTO ─────────
def solve(emps: List[Emp], dem: List[Demand], week: List[date],
          overrides_emp_day: Set[Tuple[str, date]]):
    relax_groups = groups_without_usershift_candidates(emps, dem, overrides_emp_day)
    mdl = cp_model.CpModel()
    X = build_variables(mdl, emps, dem, overrides_emp_day, relax_groups)
    if not X: raise ScheduleGenerationError("Sin variables: reglas dejan todo vacío.")

    # demanda exacta
    for d in dem:
        mdl.Add(sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X) == d.need)

    # no solape
    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    for lst in by_day.values():
        lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # 9h/día, días/sem, descanso 9h
    for e in emps:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                mdl.Add(sum(duration_min(dm) * X[e.id, dm.id] for dm in todays) <= MAX_HOURS_PER_DAY * 60)
        mdl.Add(sum(X[e.id, d.id] for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)

    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id,a.id) in X and (e.id,b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id,a.id] + X[e.id,b.id] <= 1)

    add_max2_blocks_per_day(mdl, emps, dem, X)

    # “al menos 1 por (día, puesto)” (penalización fuerte si vacío)
    groups = defaultdict(list)
    for d in dem: groups[(d.date, d.wsid)].append(d)
    group_has_cover = {}
    group_penalties = []
    for gk, dlist in groups.items():
        gvar = mdl.NewBoolVar(f"grp_cover_{gk[0].isoformat()}_{gk[1]}")
        group_has_cover[gk] = gvar
        for d in dlist:
            for e in emps:
                if (e.id, d.id) in X:
                    mdl.AddImplication(X[e.id, d.id], gvar)
        group_penalties.append(1 - gvar)

    mdl.Minimize(sum(group_penalties) * WEIGHT_MUST_HAVE_ONE)

    sol = cp_model.CpSolver()
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
                   overrides: Set[Tuple[str,date]]):
    mdl = cp_model.CpModel()
    X = build_variables_with_usershift_logic(mdl, emps, dem, overrides)
    if not X: raise ScheduleGenerationError("Sin variables viables tras reglas.")

    unmet = {d.id: mdl.NewIntVar(0, d.need, f"unmet_{d.id}") for d in dem}
    for d in dem:
        covered = sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X)
        mdl.Add(covered + unmet[d.id] == d.need)

    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    for lst in by_day.values():
        lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    overtimes = []
    for e in emps:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                total_min_today = sum(duration_min(dm) * X[e.id, dm.id] for dm in todays)
                ot = mdl.NewIntVar(0, 24*60, f"ot_{e.id}_{dday.isoformat()}")
                mdl.Add(ot >= total_min_today - MAX_HOURS_PER_DAY * 60)
                mdl.Add(ot >= 0)
                overtimes.append(ot)

    for e in emps:
        mdl.Add(sum(X[e.id, d.id] for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)

    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id,a.id) in X and (e.id,b.id) in X:
                    rest = (24*60 - _t2m(a.end)) + _t2m(b.start)
                    if rest < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id,a.id] + X[e.id,b.id] <= 1)

    add_max2_blocks_per_day(mdl, emps, dem, X)

    groups = defaultdict(list)
    for d in dem: groups[(d.date, d.wsid)].append(d)
    group_uncovered = []
    for gk, dlist in groups.items():
        gvar = mdl.NewBoolVar(f"grp_has_cover_{gk[0].isoformat()}_{gk[1]}")
        at_least_one = []
        for d in dlist:
            for e in emps:
                if (e.id, d.id) in X: at_least_one.append(X[e.id, d.id])
        if at_least_one:
            mdl.Add(sum(at_least_one) >= gvar)
            for v in at_least_one: mdl.AddImplication(v, gvar)
            group_uncovered.append(1 - gvar)

    weights = {d.id: (WEIGHT_ULTRA_SLOT0 if d.slot_index==0 else (WEIGHT_SHORT_SLOT if duration_min(d)<=15 else max(1, 60000//max(1,duration_min(d))))) for d in dem}
    total_unmet_weighted = sum(weights[d.id] * unmet[d.id] for d in dem)
    total_unmet_minutes  = sum(duration_min(d) * unmet[d.id] for d in dem)
    total_overtime       = sum(overtimes) if overtimes else 0
    must_have_one_pen    = sum(group_uncovered) * WEIGHT_MUST_HAVE_ONE

    mdl.Minimize(must_have_one_pen * 1000 + total_unmet_weighted * 100 + total_unmet_minutes * 1 + total_overtime * 5)

    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = 120
    status = sol.Solve(mdl)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE): raise ScheduleGenerationError("Modelo sin solución factible (flexible)")

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

# ───────── OBS / GENERATE ─────────
def merge_intervals(intervals):
    if not intervals: return []
    intervals.sort(); merged = [intervals[0]]
    for s,e in intervals[1:]:
        ls,le = merged[-1]
        if s <= le: merged[-1] = (ls, max(le,e))
        else: merged.append((s,e))
    return merged

def to_min_t(t: time) -> int: return t.hour*60 + t.minute

def count_blocks_for_employee_day(assigns_day_emp):
    intervals = []
    for dm in assigns_day_emp:
        s = to_min_t(dm.start); e = to_min_t(dm.end) if dm.end != time(0,0) else 24*60
        if e < s: e += 24*60
        intervals.append((s,e))
    return len(merge_intervals(intervals))

def calc_obs(emp: Emp, dm: Demand, assigns_day: list, fixed_ids: set):
    if (emp.id, dm.id) in fixed_ids: return ""
    todays_emp_dms = [d for e, d in assigns_day if e.id == emp.id and d.wsid is not None]
    blocks = count_blocks_for_employee_day(todays_emp_dms)
    return "C" if blocks >= 2 else "BT"

def generate(week_start: date):
    emps, demands, tpl, week, fixed, _ = load_data(week_start)
    overrides = compute_usershift_free_overrides(emps, demands, week)
    sched, relaxed_groups = solve(emps, demands, week, overrides)

    for d, lst in fixed.items(): sched[d].extend(lst)
    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {"id": uid(), "wsid": None, "wsname": "AUSENCIA",
                                                "start": time(0,0), "end": time(0,0), "date": d})()
                sched[d].append((emp, pseudo_dm))

    total_req = sum(dm.need for dm in demands) + len(fixed_ids)
    total_ass = sum(len(v) for v in sched.values())

    overrides_list = [{"employee_id": str(eid),
                       "employee_name": next((e.name for e in emps if e.id == eid), ""),
                       "date": d.isoformat()} for (eid, d) in sorted(overrides, key=lambda x: (x[1], str(x[0])))]

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
            "relaxed_groups_for_must_have_one": relaxed_list
        },
        "schedule": {}
    }
    for d in week:
        k = d.isoformat(); res["schedule"][k] = []
        for emp, dm in sched.get(d, []):
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
    emps, demands, tpl, week, fixed, _ = load_data(week_start)
    overrides = compute_usershift_free_overrides(emps, demands, week)
    sched, coverage_stats = solve_flexible(emps, demands, week, overrides)

    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {"id": uid(), "wsid": None, "wsname": "AUSENCIA",
                                                "start": time(0,0), "end": time(0,0), "date": d})()
                sched[d].append((emp, pseudo_dm))

    total_req = sum(dm.need for dm in demands)
    total_cov = sum(s["covered"] for s in coverage_stats.values())
    total_unmet = sum(s["unmet"] for s in coverage_stats.values())
    overrides_list = [{"employee_id": str(eid),
                       "employee_name": next((e.name for e in emps if e.id == eid), ""),
                       "date": d.isoformat()} for (eid, d) in sorted(overrides, key=lambda x: (x[1], str(x[0])))]
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
            "usershift_free_overrides": overrides_list
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
        for emp, dm in sched.get(d, []):
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

# ───────── ENDPOINTS ─────────
@app.route('/api/health')
def health():
    st = {"status":"checking","timestamp":now().isoformat(),"version":"3.13","checks":{}}
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
        res, _, _, _, _ = (generate_flexible(ws) if flexible else generate(ws))
        return jsonify(res), 200
    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
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
    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
        return jsonify({"error": str(e)}), 400

    try:
        with conn() as c, c.cursor() as cur:
            cur.execute('SELECT COUNT(*) FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s', (ws, we))
            if cur.fetchone()[0] and not force:
                return jsonify({"error": "Horario ya existe para esa semana"}), 409
            if force:
                cur.execute('DELETE FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s', (ws, we))

            for d, ass in sched.items():
                for emp, dm in ass:
                    if dm.wsid is None:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId","StartTime","EndTime","Observation","IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (uid(), d, str(emp.id), None, None, None, emp.abs_reason.get(d,'ABS'), False, now()))
                    else:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId","StartTime","EndTime","Observation","IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (
                            uid(), d, str(emp.id), str(dm.wsid),
                            timedelta(hours=dm.start.hour, minutes=dm.start.minute),
                            timedelta(hours=dm.end.hour,   minutes=dm.end.minute),
                            calc_obs(emp, dm, ass, fixed_ids), False, now()
                        ))
            c.commit()
    except Exception as e:
        return jsonify({"error": "Error al guardar", "detail": str(e)}), 500

    return jsonify({"message": ("Horario guardado (flexible)" if flexible else "Horario guardado"), **res}), 201

# ───────── MAIN ─────────
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
if __name__ == "__main__":
    print("API Gandarias v3.13 en http://localhost:5000")
    print("UserShifts: se cortan demandas en los BORDES de las ventanas, p.ej. 12–14 ⇒ 12–13 y 13–14.")
    app.run(host="0.0.0.0", port=5000, debug=True)
