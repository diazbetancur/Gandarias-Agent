#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGENDA GENERATOR API – Gandarías v4.0 (UserShifts EXACTOS y BLOQUEO si no hay match)

Reglas clave v4.0
• UserShifts son OBLIGATORIOS por día:
  - Si hay demanda(s) que encajan EXACTAMENTE con el/los bloques declarados ese día, SOLO se permiten esas demandas y se exige cubrir ≥1.
  - Si NO hay ninguna demanda que encaje ese día, el empleado queda BLOQUEADO ese día (no se le asigna nada).
• Se mantienen mejoras previas: normalización de necesidad por MAX(need), segmentación ≤9h, prioridad “al menos 1 por puesto/día” (en flexible), etc.
"""

import logging
import uuid
from collections import defaultdict
from datetime import date, datetime, time, timedelta, timezone
from typing import List, Tuple

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
MAX_DAYS_PER_WEEK = 6
MAX_HOURS_PER_DAY = 9
MAX_SHIFT_DURATION_HOURS = 9

# Pesos / penalizaciones (modo flexible)
WEIGHT_MUST_HAVE_ONE = 200_000
WEIGHT_ULTRA_SLOT0 = 500_000
WEIGHT_SHORT_SLOT = 100_000

# ───────── FLASK APP ─────────
app = Flask(__name__)
CORS(app)

# ───────── BD CONFIG ─────────
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
        self.roles = set()
        self.day_off = set()              # días libres por DOW (0=lun..6=dom) – usamos weekday() de Python
        self.window = defaultdict(list)   # DOW -> [(start,end)]
        self.exc = defaultdict(list)      # fecha -> [(start,end)]
        self.absent = set()               # fechas de ausencia
        self.abs_reason = {}              # fecha -> 'VAC'|'ABS'
        # UserShifts
        self.user_shifts = defaultdict(set)       # DOW -> {ShiftTypeId} (solo informativo/diagnóstico)
        self.user_shifts_data = defaultdict(list) # DOW -> list[{structure, block1_start, block1_end, block2_start, block2_end}]
        # Prohibiciones explícitas por ShiftType (si las usas)
        self.shift_type_restrictions = set()

    def can(self, ws):
        return ws in self.roles

    def off(self, d: date) -> bool:
        return d.weekday() in self.day_off

    def absent_day(self, d: date) -> bool:
        return d in self.absent

    def available(self, d: date, s: time, e: time) -> bool:
        # Sin restricciones → disponible
        if not self.day_off and not self.window and not self.exc:
            return True
        if self.off(d) or self.absent_day(d):
            return False
        pg_dow = d.weekday()
        win = self.exc.get(d) or self.window.get(pg_dow)
        if not win:
            return False
        end = e if e != time(0, 0) else time(23, 59)
        for a, b in win:
            if s >= a and end <= b:
                return True
        return False


class Demand:
    def __init__(self, row: Tuple):
        (self.id, rdate, self.wsid, self.wsname, self.start, self.end, need) = row
        self.date = rdate.date() if hasattr(rdate, 'date') else rdate
        self.need = int(need)
        self.slot_index = 0  # orden horario dentro del día/puesto


# ───────── HELPERS TIEMPO ─────────
def _t2m(t: time) -> int:
    return (0 if t is None else t.hour * 60 + t.minute)

def _t2m_end(t: time) -> int:
    # Para límites derechos: 00:00 se interpreta como 24:00
    return 24*60 if (t is not None and t == time(0, 0)) else _t2m(t)

def _m2t(m: int) -> time:
    m = max(0, min(24*60, m))
    return time(m // 60, m % 60) if m < 24*60 else time(0, 0)

def duration_min(dm: Demand) -> int:
    start = _t2m(dm.start)
    end = _t2m(dm.end) if dm.end != time(0, 0) else 24*60
    if end < start:  # cruza medianoche
        end += 24*60
    return end - start

# ───────── INTERVAL/FIT HELPERS ─────────
def _fits(b_start, b_end, st_start, st_end):
    return (b_start and b_end and st_start and st_end and
            _t2m(st_start) <= _t2m(b_start) and _t2m_end(b_end) <= _t2m_end(st_end))

def demand_matches_usershift_blocks(demand: Demand, user_shift_data: dict) -> bool:
    """Demanda contenida dentro de B1 o B2 del UserShift (exact match por contención)."""
    ds = _t2m(demand.start)
    de = _t2m_end(demand.end)

    if user_shift_data.get('structure') == 0:
        b1s = _t2m(user_shift_data['block1_start'])
        b1e = _t2m_end(user_shift_data['block1_end'])
        return (b1s is not None and b1e is not None and ds >= b1s and de <= b1e)

    # Partido: basta con que caiga entero en B1 o entero en B2
    b1s = _t2m(user_shift_data['block1_start'])
    b1e = _t2m_end(user_shift_data['block1_end'])
    if b1s is not None and b1e is not None and ds >= b1s and de <= b1e:
        return True
    b2s = _t2m(user_shift_data['block2_start'])
    b2e = _t2m_end(user_shift_data['block2_end'])
    if b2s is not None and b2e is not None and ds >= b2s and de <= b2e:
        return True
    return False

# ───────── DEMANDS PROCESSING ─────────
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
    """Une demandas contiguas (mismo need) sin exceder 9h."""
    by_key = defaultdict(list)
    for d in demands:
        by_key[(d.date, d.wsid, d.wsname)].append(d)

    merged = []
    for (dte, wsid, wsname), items in by_key.items():
        items.sort(key=lambda x: (_t2m(x.start), _t2m(x.end)))
        if not items:
            continue
        curr = items[0]
        for nxt in items[1:]:
            pot_dur_min = _t2m(nxt.end if nxt.end != time(0,0) else time(23,59)) - _t2m(curr.start)
            pot_dur_h = pot_dur_min / 60.0
            if (nxt.need == curr.need
                and _t2m(nxt.start) - _t2m(curr.end) <= tolerate_gap_min
                and pot_dur_h <= MAX_SHIFT_DURATION_HOURS):
                curr.end = nxt.end
            else:
                merged.append(curr)
                curr = nxt
        merged.append(curr)

    out = []
    for d in merged:
        out.append(Demand((d.id, d.date, d.wsid, d.wsname, d.start, d.end, d.need)))
    return out

def normalize_by_max_need_profile(demands):
    """Para cada día/puesto crea franjas con MAX(need) (elimina suma por solapes)."""
    if not ENFORCE_PEAK_CAP:
        return demands

    grouped = defaultdict(list)
    for d in demands:
        grouped[(d.date, d.wsid, d.wsname)].append(d)

    out = []
    for (dte, wsid, wsname), items in grouped.items():
        cuts = set()
        for it in items:
            s = _t2m(it.start)
            e = _t2m(it.end) if it.end != time(0, 0) else 24*60
            cuts.add(s); cuts.add(e)
        cuts = sorted(cuts)
        if len(cuts) <= 1:
            continue

        segments = []
        over_sum_detected = False
        for i in range(len(cuts)-1):
            a, b = cuts[i], cuts[i+1]
            if a >= b:
                continue
            active = []
            for it in items:
                s = _t2m(it.start)
                e = _t2m(it.end) if it.end != time(0, 0) else 24*60
                if s <= a and e >= b:
                    active.append(it.need)
            if not active:
                continue
            max_need = max(active)
            sum_need = sum(active)
            if sum_need > max_need:
                over_sum_detected = True
            segments.append((a, b, max_need))

        # fusionar contiguos con mismo need
        fused = []
        for seg in segments:
            if not fused:
                fused.append(seg)
            else:
                la, lb, ln = fused[-1]
                a, b, n = seg
                if ln == n and a == lb:
                    fused[-1] = (la, b, n)
                else:
                    fused.append(seg)

        # cortar a <= 9h
        for a, b, n in fused:
            if n <= 0 or a >= b:
                continue
            if (b - a) <= MAX_SHIFT_DURATION_HOURS * 60:
                out.append(Demand((uid(), dte, wsid, wsname, _m2t(a), _m2t(b if b < 24*60 else 0), n)))
            else:
                out.extend(split_long_segment(dte, wsid, wsname, a, b, n, MAX_SHIFT_DURATION_HOURS))

        if over_sum_detected and PEAK_CAP_LOG:
            print(f"[NORMALIZACION] {dte} {wsname}: solapes reducidos usando MAX(need).")

    return out

def set_slot_indexes(demands):
    by_day_ws = defaultdict(list)
    for d in demands:
        by_day_ws[(d.date, d.wsid)].append(d)
    for (_, _), lst in by_day_ws.items():
        lst.sort(key=lambda x: (_t2m(x.start), _t2m(x.end)))
        for idx, d in enumerate(lst):
            d.slot_index = idx

def to_min(t): return t.hour*60 + t.minute
def overlap(a, b): return not (a.end <= b.start or b.end <= a.start)

# ───────── OBJETIVO: PESOS (flex) ─────────
def demand_weight(dm: Demand) -> int:
    dur = max(1, duration_min(dm))
    if dm.slot_index == 0:
        return WEIGHT_ULTRA_SLOT0
    if dur <= 15:
        return WEIGHT_SHORT_SLOT
    return max(1, 60000 // dur)

# ───────── BD ─────────
def conn():
    try:
        return psycopg2.connect(**DB)
    except OperationalError as e:
        t = str(e)
        if "could not connect" in t:
            raise DatabaseConnectionError("No se puede conectar al servidor de BD")
        if "authentication failed" in t:
            raise DatabaseConnectionError("Credenciales de BD incorrectas")
        raise DatabaseConnectionError(t)

def fetchall(cur, sql, pars=()):
    try:
        cur.execute(sql, pars)
        return cur.fetchall()
    except (ProgrammingError, DataError) as e:
        raise DataIntegrityError(str(e))

def monday(d: date) -> date:
    while d.weekday() != 0:
        d -= timedelta(days=1)
    return d

def pick_template(cur, week_start: date, week_end: date):
    print("="*60)
    print(f"[PICK_TEMPLATE] Semana {week_start} a {week_end}")
    print("="*60)

    act = fetchall(cur, '''
        SELECT "Id","Name"
        FROM "Management"."WorkstationDemandTemplates"
        WHERE "IsActive" = TRUE
    ''')
    if len(act) == 1:
        print(f"[PICK_TEMPLATE] Plantilla activa: '{act[0][1]}'")
        return act[0]
    elif len(act) > 1:
        raise DataIntegrityError("Hay varias plantillas activas; debe haber solo una")
    else:
        print("[PICK_TEMPLATE] No hay plantilla activa; se elige por cercania...")

    rows = fetchall(cur, '''
        SELECT 
            t."Id",
            t."Name",
            t."StartDate"::date,
            t."EndDate"::date,
            COALESCE(t."DateCreated", '-infinity'::timestamptz) AS created,
            (SELECT COUNT(*) FROM "Management"."WorkstationDemands" d WHERE d."TemplateId" = t."Id") AS demandas
        FROM "Management"."WorkstationDemandTemplates" t
        WHERE t."StartDate" IS NOT NULL AND t."EndDate" IS NOT NULL
    ''')
    if not rows:
        raise DataNotFoundError("No existen plantillas con StartDate/EndDate")

    def md(x: date): return (x.month, x.day)
    def same_year(year: int, m: int, d: int) -> date:
        try:
            return date(year, m, d)
        except ValueError:
            return date(year, 2, 28) if (m == 2 and d == 29) else date(year, m, d)

    week_center = week_start + (week_end - week_start) // 2

    def distance_metrics(start_md, end_md):
        y = week_start.year
        s = same_year(y, start_md[0], start_md[1])
        e = same_year(y, end_md[0],   end_md[1])
        segments = [(s, e)] if s <= e else [(s, date(y,12,31)), (date(y,1,1), e)]
        def seg_dist(a, b):
            if not (b < week_start or a > week_end):
                return (0, 0)
            if b < week_start:
                return ((week_start - b).days, abs((week_center - b).days))
            else:
                return ((a - week_end).days, abs((a - week_center).days))
        return min((seg_dist(a, b) for (a, b) in segments), key=lambda x: (x[0], x[1]))

    scored = []
    for tid, name, sdate, edate, created, demandas in rows:
        dist, dcenter = distance_metrics(md(sdate), md(edate))
        scored.append({
            "id": tid, "name": name, "start": sdate, "end": edate,
            "created": created, "demandas": int(demandas or 0),
            "dist": dist, "dcenter": dcenter
        })
    scored.sort(key=lambda r: (r["dist"], r["dcenter"]))

    chosen = next((r for r in scored if r["demandas"] > 0), None)
    if chosen:
        print(f"[PICK_TEMPLATE] Elegida: '{chosen['name']}' (con demandas>0)")
        return (chosen["id"], chosen["name"])

    raise DataNotFoundError("No se encontró plantilla con demandas > 0")

# ───────── CARGA DATOS ─────────
def load_data(week_start: date):
    week = [week_start + timedelta(days=i) for i in range(7)]
    week_end = week[-1]

    # Helpers para cast tiempos
    def _to_time(x):
        if x is None:
            return None
        if isinstance(x, time):
            return x
        if isinstance(x, timedelta):
            return (datetime.min + x).time()
        try:
            return (datetime.min + x).time()
        except Exception:
            return None

    def _pair(s, e):
        s, e = _to_time(s), _to_time(e)
        if not s or not e:
            return None
        e = e if e != time(0, 0) else time(23, 59)
        return (s, e) if s < e else None

    def _complement_blocks(blocks):
        DAY_START, DAY_END = time(0, 0), time(23, 59)
        ivs = []
        for p in blocks:
            if p: ivs.append(p)
        ivs.sort(key=lambda p: (p[0], p[1]))
        merged = []
        for s, e in ivs:
            if not merged:
                merged.append([s, e])
            else:
                ls, le = merged[-1]
                if s <= le:
                    merged[-1][1] = max(le, e)
                else:
                    merged.append([s, e])
        out = []
        cur = DAY_START
        for s, e in merged:
            if cur < s:
                out.append((cur, (s if s != time(0,0) else time(23,59))))
            cur = max(cur, e)
        if cur < DAY_END:
            out.append((cur, DAY_END))
        return out

    with conn() as c, c.cursor() as cur:
        # ── plantilla y demandas
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

        demands = coalesce_demands(demands, tolerate_gap_min=0)
        demands = normalize_by_max_need_profile(demands)
        set_slot_indexes(demands)
        if not demands:
            raise DataNotFoundError("La plantilla seleccionada no tiene demandas")

        # ── empleados y roles
        emps = {r[0]: Emp(r) for r in fetchall(cur, '''
            SELECT "Id",
                   COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                   COALESCE("ComplementHours", TRUE)
            FROM "Management"."AspNetUsers"
            WHERE "IsActive" AND NOT "IsDelete"
        ''')}
        if not emps:
            raise DataNotFoundError("No hay empleados activos")

        for uid, ws in fetchall(cur, '''
            SELECT "UserId","WorkstationId"
            FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete"
        '''):
            if uid in emps:
                emps[uid].roles.add(ws)
        if not any(e.roles for e in emps.values()):
            raise DataNotFoundError("Ningún empleado tiene roles asignados")

        # ── restricciones semanales
        print("\n[DEBUG] Cargando restricciones")
        day_names = ['Domingo','Lunes','Martes','Miercoles','Jueves','Viernes','Sabado']

        for uid, dow, rt, f1, t1, b1s, b1e, b2s, b2e in fetchall(cur, '''
            SELECT "UserId","DayOfWeek","RestrictionType",
                   "AvailableFrom","AvailableUntil",
                   "Block1Start","Block1End",
                   "Block2Start","Block2End"
            FROM "Management"."EmployeeScheduleRestrictions"
        '''):
            if uid not in emps:
                continue
            emp = emps[uid]

            if rt == 0:
                emp.day_off.add(dow)
                print(f"[DEBUG] {emp.name} NO TRABAJA {day_names[dow]}")
                continue

            if rt == 1:
                emp.window[dow].append((time(0,0), time(23,59)))
                continue

            if rt == 2:
                s = _to_time(f1); e = _to_time(t1)
                if s is None and e is None:
                    continue
                if s is not None and e is None:
                    e = time(23, 59)
                if s is None and e is not None:
                    s = time(0, 0)
                if e == time(0, 0):
                    e = time(23, 59)
                if s < e:
                    emp.window[dow].append((s, e))
                continue

            if rt == 3:
                t = _to_time(t1)
                if t:
                    emp.window[dow].append((time(0,0), t if t != time(0,0) else time(23,59)))
                continue

            if rt == 4:
                p1 = _pair(b1s, b1e)
                p2 = _pair(b2s, b2e)
                any_added = False
                if p1:
                    emp.window[dow].append(p1); any_added = True
                if p2:
                    emp.window[dow].append(p2); any_added = True
                if not any_added:
                    p = _pair(f1, t1)
                    if p:
                        emp.window[dow].append(p)
                continue

            if rt == 5:
                blocked = []
                p1 = _pair(b1s, b1e)
                p2 = _pair(b2s, b2e)
                if p1: blocked.append(p1)
                if p2: blocked.append(p2)
                if not blocked:
                    p = _pair(f1, t1)
                    if p: blocked.append(p)
                comp = _complement_blocks(blocked)
                for w in comp:
                    emp.window[dow].append(w)
                continue

            print(f"[ADVERTENCIA] Tipo de restricción desconocido rt={rt} para {emp.name} {day_names[dow]}")

        # ── excepciones puntuales por fecha
        for uid, d, rt, f, t in fetchall(cur, '''
            SELECT "UserId","Date","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s
        ''', (week_start, week_end)):
            if uid not in emps:
                continue
            emp = emps[uid]
            if rt == 0:
                emp.absent.add(d)
                emp.abs_reason[d] = 'ABS'
            else:
                p = _pair(f, t)
                if p:
                    emp.exc[d].append(p)

        # ── licencias y ausentismos
        for uid, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date,
                   COALESCE("EndDate"::date,%s)
            FROM "Management"."Licenses"
            WHERE "StartDate"::date <= %s
              AND COALESCE("EndDate"::date,%s) >= %s
        ''', (week_end, week_end, week_end, week_start)):
            if uid not in emps:
                continue
            emp = emps[uid]
            d = max(sd, week_start)
            while d <= ed:
                emp.absent.add(d); emp.abs_reason[d] = 'VAC'
                d += timedelta(days=1)

        for uid, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date,
                   COALESCE("EndDate"::date,%s)
            FROM "Management"."UserAbsenteeisms"
            WHERE "StartDate"::date <= %s
              AND COALESCE("EndDate"::date,%s) >= %s
        ''', (week_end, week_end, week_end, week_start)):
            if uid not in emps:
                continue
            emp = emps[uid]
            d = max(sd, week_start)
            while d <= ed:
                emp.absent.add(d); emp.abs_reason[d] = 'ABS'
                d += timedelta(days=1)

        # ── ShiftTypes (opcional / diagnóstico)
        shift_types = []
        for row in fetchall(cur, '''
            SELECT "Id","Name","Description",
                    (TIMESTAMP '2000-01-01' + "Block1Start")::time       AS b1_start,
                    (TIMESTAMP '2000-01-01' + "Block1lastStart")::time   AS b1_end,
                    (TIMESTAMP '2000-01-01' + "Block2Start")::time       AS b2_start,
                    (TIMESTAMP '2000-01-01' + "Block2lastStart")::time   AS b2_end,
                    "Structure" = 1 AS is_split,
                    "IsActive"
                FROM "Management"."ShiftTypes"
                WHERE "IsActive" = TRUE
        '''):
            shift_types.append({
                'id': row[0], 'name': row[1], 'description': row[2],
                'b1_start': row[3], 'b1_end': row[4],
                'b2_start': row[5], 'b2_end': row[6],
                'is_split': row[7], 'is_active': row[8],
            })

        print(f"\n[DEBUG] Cargados {len(shift_types)} ShiftTypes activos")

        # ── UserShifts: almacenar bloques por DOW y construir coincidencias EXACTAS por (emp, fecha)
        user_shifts_count = 0
        for uid, day, structure, b1s, b1e, b2s, b2e in fetchall(cur, '''
            SELECT "UserId", "Day", "Structure", 
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time AS block1_start,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time AS block1_end,
                   (TIMESTAMP '2000-01-01' + "Block2Start")::time AS block2_start,
                   (TIMESTAMP '2000-01-01' + "Block2lastStart")::time AS block2_end
            FROM "Management"."UserShifts"
        '''):
            if uid in emps:
                usd = {
                    'structure': structure,
                    'block1_start': b1s if b1s else None,
                    'block1_end':   b1e if b1e else None,
                    'block2_start': b2s if b2s else None,
                    'block2_end':   b2e if b2e else None
                }
                emps[uid].user_shifts_data[day].append(usd)
                user_shifts_count += 1

                # mapear STs posibles (informativo)
                for st in shift_types:
                    b1_ok = _fits(b1s, b1e, st['b1_start'], st['b1_end']) or _fits(b1s, b1e, st['b2_start'], st['b2_end'])
                    b2_ok = _fits(b2s, b2e, st['b1_start'], st['b1_end']) or _fits(b2s, b2e, st['b2_start'], st['b2_end'])
                    if (structure == 0 and b1_ok) or (structure == 1 and (b1_ok or b2_ok)):
                        emps[uid].user_shifts[day].add(st['id'])

        print(f"[DEBUG] Total UserShifts cargados: {user_shifts_count}")

        # Coincidencias EXACTAS: (emp_id, fecha_real) -> [demand_id,...]
        exact_matches = defaultdict(list)
        for e in emps.values():
            for d in week:
                dow = d.weekday()
                if not e.user_shifts_data.get(dow):
                    continue
                for dm in demands:
                    if dm.date != d or not e.can(dm.wsid):
                        continue
                    # encaje con alguno de sus bloques declarados ese DOW
                    for usd in e.user_shifts_data[dow]:
                        if demand_matches_usershift_blocks(dm, usd):
                            exact_matches[(e.id, d)].append(dm.id)
                            break  # ya encajó con un bloque

        return list(emps.values()), demands, tpl_name, week, {}, shift_types, exact_matches

# ───────── RESTRICCIONES AUX ─────────
def add_max2_blocks_per_day(mdl, emps, dem, X):
    """Máximo 2 bloques disjuntos por día y empleado (aprox)."""
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    def disjoint(a, b):
        return (a.end <= b.start) or (b.end <= a.start)

    for e in emps:
        for day, lst in by_day.items():
            lst_sorted = sorted(lst, key=lambda d: (d.start, d.end))
            n = len(lst_sorted)
            for i in range(n):
                for j in range(i+1, n):
                    a, b = lst_sorted[i], lst_sorted[j]
                    if not disjoint(a, b):
                        continue
                    for k in range(j+1, n):
                        c = lst_sorted[k]
                        if not disjoint(b, c) or not disjoint(a, c):
                            continue
                        if (e.id, a.id) in X and (e.id, b.id) in X and (e.id, c.id) in X:
                            mdl.Add(X[e.id, a.id] + X[e.id, b.id] + X[e.id, c.id] <= 2)

def add_mandatory_usershift_constraints(mdl, emps, dem, X, exact_matches):
    """
    Si hay match exacto para (empleado, fecha) -> exigir cubrir >=1 de esas demandas.
    """
    print("\n[CONSTRAINTS] UserShift OBLIGATORIO cuando hay match exacto...")
    added = 0
    for (emp_id, date_key), demand_ids in exact_matches.items():
        vars_ok = [X[emp_id, d_id] for d_id in demand_ids if (emp_id, d_id) in X]
        if vars_ok:
            mdl.Add(sum(vars_ok) >= 1)
            added += 1
    print(f"[CONSTRAINTS] Restricciones añadidas: {added}")

# ───────── SOLVER ESTRICTO ─────────
def solve(emps: List[Emp], dem: List[Demand], week: List[date], exact_matches: dict):
    mdl = cp_model.CpModel()
    X = {}

    creation_stats = {
        'total_combinations': 0,
        'basic_restrictions': 0,
        'usershift_blocked': 0,
        'variables_created': 0
    }

    # Creación de variables con regla EXACTA/BLOQUEO
    for d in dem:
        for e in emps:
            creation_stats['total_combinations'] += 1

            # Rol siempre requerido
            if not e.can(d.wsid):
                creation_stats['basic_restrictions'] += 1
                continue

            dow = d.date.weekday()
            has_usershift_today = bool(e.user_shifts_data.get(dow))
            key = (e.id, d.date)

            if has_usershift_today:
                # Si el empleado TIENE UserShift ese día:
                if key in exact_matches:
                    # Solo permitir las demandas que encajan EXACTO con su bloque
                    if d.id not in exact_matches[key]:
                        creation_stats['usershift_blocked'] += 1
                        continue
                    # Respeta solo “día libre” y “ausente”; la disponibilidad se deriva del UserShift
                    if e.off(d.date) or e.absent_day(d.date):
                        creation_stats['basic_restrictions'] += 1
                        continue
                    # OK: crear variable (no pasamos por available())
                    X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
                    creation_stats['variables_created'] += 1
                else:
                    # Tiene UserShift pero NO hay match exacto → BLOQUEA el día completo (nada ese día)
                    creation_stats['usershift_blocked'] += 1
                    continue
            else:
                # Día sin UserShift → flujo normal (requiere disponibilidad semanal/diaria)
                if not e.available(d.date, d.start, d.end) or e.absent_day(d.date) or e.off(d.date):
                    creation_stats['basic_restrictions'] += 1
                    continue
                X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
                creation_stats['variables_created'] += 1



    print(f"\n[DEBUG] Vars: totalComb={creation_stats['total_combinations']} "
          f"basicBlock={creation_stats['basic_restrictions']} "
          f"userShiftBlock={creation_stats['usershift_blocked']} "
          f"created={creation_stats['variables_created']}")

    if not X:
        raise ScheduleGenerationError("Sin variables: las restricciones impiden toda asignación")

    # Exigir cubrir ≥1 donde haya match exacto
    add_mandatory_usershift_constraints(mdl, emps, dem, X, exact_matches)

    # cubrir demanda exactamente
    for d in dem:
        mdl.Add(sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X) == d.need)

    # no solapamientos
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)
    for lst in by_day.values():
        lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # 9h por día
    for e in emps:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                mdl.Add(sum(duration_min(dm) * X[e.id, dm.id] for dm in todays) <= MAX_HOURS_PER_DAY * 60)

    # max días/semana
    for e in emps:
        mdl.Add(sum(X[e.id, d.id] for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)

    # descanso entre días (>=9h)
    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id, a.id) in X and (e.id, b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    add_max2_blocks_per_day(mdl, emps, dem, X)

    # objetivo trivial (solo factibilidad)
    mdl.Minimize(0)

    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = 120
    if sol.Solve(mdl) not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ScheduleGenerationError("Modelo sin solución")

    out = defaultdict(list)
    for d in dem:
        for e in emps:
            if (e.id, d.id) in X and sol.Value(X[e.id, d.id]):
                out[d.date].append((e, d))
    return out

# ───────── SOLVER FLEXIBLE ─────────
def solve_flexible(emps: List[Emp], dem: List[Demand], week: List[date], exact_matches: dict):
    mdl = cp_model.CpModel()
    X = {}

    cand_count = defaultdict(int)
    creation_stats = {
        'total_combinations': 0,
        'basic_restrictions': 0,
        'usershift_blocked': 0,
        'variables_created': 0
    }

    for d in dem:
        for e in emps:
            creation_stats['total_combinations'] += 1

            # Rol siempre requerido
            if not e.can(d.wsid):
                creation_stats['basic_restrictions'] += 1
                continue

            dow = d.date.weekday()
            has_usershift_today = bool(e.user_shifts_data.get(dow))
            key = (e.id, d.date)

            if has_usershift_today:
                if key in exact_matches:
                    if d.id not in exact_matches[key]:
                        creation_stats['usershift_blocked'] += 1
                        continue
                    if e.off(d.date) or e.absent_day(d.date):
                        creation_stats['basic_restrictions'] += 1
                        continue
                    # OK: crear variable (saltamos available())
                    X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
                    cand_count[d.id] += 1
                    creation_stats['variables_created'] += 1
                else:
                    creation_stats['usershift_blocked'] += 1
                    continue
            else:
                if not e.available(d.date, d.start, d.end) or e.absent_day(d.date) or e.off(d.date):
                    creation_stats['basic_restrictions'] += 1
                    continue
                X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
                cand_count[d.id] += 1
                creation_stats['variables_created'] += 1


    print(f"\n[DEBUG FLEX] Vars: total={creation_stats['total_combinations']} "
          f"basicBlock={creation_stats['basic_restrictions']} "
          f"userShiftBlock={creation_stats['usershift_blocked']} "
          f"created={creation_stats['variables_created']}")

    if not X:
        raise ScheduleGenerationError("Sin variables: las restricciones impiden toda asignación")

    # Evidencia: demandas sin candidatos
    for d in dem:
        if cand_count[d.id] == 0:
            print(f"[EVIDENCIA] Sin candidatos: {d.wsname} {d.date} {d.start.strftime('%H:%M')}-{d.end.strftime('%H:%M')} need={d.need}")

    # Demanda no cubierta
    unmet_demand = {d.id: mdl.NewIntVar(0, d.need, f"unmet_{d.id}") for d in dem}
    for d in dem:
        covered = sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X)
        mdl.Add(covered + unmet_demand[d.id] == d.need)

    # No solapamientos
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)
    for lst in by_day.values():
        lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # 9h/día flex: overtime penalizado
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

    # max días/semana
    for e in emps:
        mdl.Add(sum(X[e.id, d.id] for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)

    # descanso entre días (>=9h)
    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id, a.id) in X and (e.id, b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    add_max2_blocks_per_day(mdl, emps, dem, X)

    # Penalización por puesto/día sin nadie (grupos)
    groups = defaultdict(list)
    for d in dem:
        groups[(d.date, d.wsid)].append(d)

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

    # Objetivo
    weights = {d.id: demand_weight(d) for d in dem}
    total_unmet_weighted = sum(weights[d.id] * unmet_demand[d.id] for d in dem)
    total_unmet_minutes  = sum(duration_min(d) * unmet_demand[d.id] for d in dem)
    total_overtime       = sum(overtimes) if overtimes else 0
    must_have_one_pen    = sum(group_penalties) * WEIGHT_MUST_HAVE_ONE

    mdl.Minimize(
        must_have_one_pen * 1000
        + total_unmet_weighted * 100
        + total_unmet_minutes * 1
        + total_overtime * 5
    )

    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = 120
    status = sol.Solve(mdl)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ScheduleGenerationError("Modelo sin solución factible")

    out = defaultdict(list)
    coverage_stats = {}

    for d in dem:
        covered = sum(1 for e in emps if (e.id, d.id) in X and sol.Value(X[e.id, d.id]))
        unmet = sol.Value(unmet_demand[d.id])
        coverage_stats[d.id] = {
            'demand': d,
            'covered': covered,
            'unmet': unmet,
            'coverage_pct': round((covered / d.need) * 100, 1) if d.need > 0 else 100
        }
        for e in emps:
            if (e.id, d.id) in X and sol.Value(X[e.id, d.id]):
                out[d.date].append((e, d))

    # Resumen en consola
    print("\n" + "="*80)
    print("REPORTE DE COBERTURA")
    print("="*80)
    total_demand = sum(d.need for d in dem)
    total_covered = sum(stats['covered'] for stats in coverage_stats.values())
    total_unmet = sum(stats['unmet'] for stats in coverage_stats.values())
    overall_coverage = round((total_covered / total_demand) * 100, 1) if total_demand > 0 else 100
    print(f"  Total demandado: {total_demand} turnos")
    print(f"  Total cubierto : {total_covered} turnos ({overall_coverage}%)")
    print(f"  Sin cubrir     : {total_unmet} turnos")
    print("="*80 + "\n")

    return out, coverage_stats

# ───────── OBSERVACIONES / UTIL ─────────
def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def to_min_t(t: time) -> int:
    return t.hour * 60 + t.minute

def count_blocks_for_employee_day(assigns_day_emp):
    intervals = []
    for dm in assigns_day_emp:
        s = to_min_t(dm.start)
        e = to_min_t(dm.end) if dm.end != time(0,0) else 24*60
        if e < s:
            e += 24*60
        intervals.append((s, e))
    return len(merge_intervals(intervals))

def calc_obs(emp: Emp, dm: Demand, assigns_day: list, fixed_ids: set):
    if (emp.id, dm.id) in fixed_ids:
        return ""
    todays_emp_dms = [d for e, d in assigns_day if e.id == emp.id and d.wsid is not None]
    blocks = count_blocks_for_employee_day(todays_emp_dms)
    return "C" if blocks >= 2 else "BT"

# ───────── GENERATE (ESTRICTO) ─────────
def generate(week_start: date):
    emps, demands, tpl, week, fixed, shift_types, exact_matches = load_data(week_start)
    sched = solve(emps, demands, week, exact_matches)

    # Inyectar asignaciones fijas (si las usas)
    for d, lst in fixed.items():
        sched[d].extend(lst)
    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    # Pseudo-demanda por AUSENCIAS
    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id": uid(), "wsid": None, "wsname": "AUSENCIA",
                    "start": time(0,0), "end": time(0,0), "date": d
                })()
                sched[d].append((emp, pseudo_dm))

    total_req = sum(dm.need for dm in demands) + len(fixed_ids)
    total_covered_real = sum(1 for lst in sched.values() for (_, dm) in lst if dm.wsid is not None)
    total_ass = sum(len(v) for v in sched.values())

    res = {
        "template": tpl,
        "week_start": week_start.isoformat(),
        "week_end": (week_start + timedelta(days=6)).isoformat(),
        "summary": {
            "total_employees": len(emps),
            "total_demands": total_req,
            "total_covered": total_covered_real,
            "total_assignments": total_ass,
            "coverage": round(total_covered_real/total_req*100, 1) if total_req else 0,
            "flexible_mode": False
        },
        "schedule": {}
    }

    for d in week:
        k = d.isoformat()
        res["schedule"][k] = []
        for emp, dm in sched.get(d, []):
            res["schedule"][k].append({
                "employee_id":      str(emp.id),
                "employee_name":    emp.name,
                "workstation_id":   (str(dm.wsid) if dm.wsid is not None else None),
                "workstation_name": dm.wsname,
                "start_time":       (dm.start.strftime("%H:%M") if dm.start else None),
                "end_time":         (dm.end.strftime("%H:%M") if dm.end else None),
                "observation":      (
                    "VAC" if dm.wsid is None and emp.abs_reason.get(d) == "VAC"
                    else "ABS" if dm.wsid is None
                    else calc_obs(emp, dm, sched[d], fixed_ids)
                )
            })
    return res, sched, emps, week, fixed_ids

# ───────── GENERATE FLEXIBLE ─────────
def generate_flexible(week_start: date):
    emps, demands, tpl, week, fixed, shift_types, exact_matches = load_data(week_start)
    sched, coverage_stats = solve_flexible(emps, demands, week, exact_matches)

    # Inyectar fijos
    for d, lst in fixed.items():
        sched[d].extend(lst)
    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    # Pseudo AUSENCIAS
    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id": uid(), "wsid": None, "wsname": "AUSENCIA",
                    "start": time(0,0), "end": time(0,0), "date": d
                })()
                sched[d].append((emp, pseudo_dm))

    total_req = sum(dm.need for dm in demands) + len(fixed_ids)
    total_covered = sum(stats['covered'] for stats in coverage_stats.values()) + len(fixed_ids)
    total_ass = sum(len(v) for v in sched.values())

    res = {
        "template": tpl,
        "week_start": week_start.isoformat(),
        "week_end":   (week_start + timedelta(days=6)).isoformat(),
        "summary": {
            "total_employees": len(emps),
            "total_demands":   total_req,
            "total_covered":   total_covered,
            "total_assignments": total_ass,
            "coverage": round(total_covered/total_req*100, 1) if total_req else 0,
            "flexible_mode": True
        },
        "coverage_details": {
            stats['demand'].id: {
                'workstation': stats['demand'].wsname,
                'date': stats['demand'].date.isoformat(),
                'time': f"{stats['demand'].start}-{stats['demand'].end}",
                'demanded': stats['demand'].need,
                'covered': stats['covered'],
                'unmet': stats['unmet'],
                'coverage_pct': stats['coverage_pct']
            } for stats in coverage_stats.values()
        },
        "schedule": {}
    }

    for d in week:
        k = d.isoformat()
        res["schedule"][k] = []
        for emp, dm in sched.get(d, []):
            res["schedule"][k].append({
                "employee_id":      str(emp.id),
                "employee_name":    emp.name,
                "workstation_id":   (str(dm.wsid) if dm.wsid is not None else None),
                "workstation_name": dm.wsname,
                "start_time":       (dm.start.strftime("%H:%M") if dm.start else None),
                "end_time":         (dm.end.strftime("%H:%M") if dm.end else None),
                "observation":      (
                    "VAC" if dm.wsid is None and emp.abs_reason.get(d) == "VAC"
                    else "ABS" if dm.wsid is None
                    else calc_obs(emp, dm, sched[d], fixed_ids)
                )
            })
    return res, sched, emps, week, fixed_ids

# ───────── ENDPOINTS ─────────
@app.route('/api/health')
def health():
    st = {"status": "checking", "timestamp": now().isoformat(),
          "version": "4.0", "checks": {}}
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute("SELECT version()")
            st["checks"]["database"] = {"status": "healthy", "version": cur.fetchone()[0].split(',')[0]}
            st["status"] = "healthy"
    except Exception as e:
        st["checks"]["database"] = {"status": "unhealthy", "message": str(e)}
        st["status"] = "unhealthy"
    return jsonify(st), 200 if st["status"] == "healthy" else 503

@app.route('/api/agenda/preview')
def preview():
    wk = request.args.get('week_start')
    flexible = request.args.get('flexible', 'true').lower() == 'true'
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    try:
        if flexible:
            res, _, _, _, _ = generate_flexible(ws)
        else:
            res, _, _, _, _ = generate(ws)
        return jsonify(res), 200
    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
        return jsonify({"error": str(e)}), 400

@app.route('/api/agenda/save', methods=['POST'])
def save():
    data = request.get_json() or {}
    wk = data.get('week_start')
    force = data.get('force', False)
    flexible = data.get('flexible', True)
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400
    we = ws + timedelta(days=6)

    try:
        if flexible:
            res, sched, emps, week, fixed_ids = generate_flexible(ws)
        else:
            res, sched, emps, week, fixed_ids = generate(ws)
    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
        return jsonify({"error": str(e)}), 400

    try:
        with conn() as c, c.cursor() as cur:
            cur.execute('''
                SELECT COUNT(*) FROM "Management"."Schedules"
                WHERE "Date" BETWEEN %s AND %s
            ''', (ws, we))
            if cur.fetchone()[0] and not force:
                return jsonify({"error": "Horario ya existe para esa semana"}), 409

            if force:
                cur.execute(
                    'DELETE FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s',
                    (ws, we)
                )

            for d, ass in sched.items():
                for emp, dm in ass:
                    if dm.wsid is None:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation",
                                 "IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (
                            uid(), d, str(emp.id), None,
                            None, None,
                            emp.abs_reason.get(d, 'ABS'),
                            False, now()
                        ))
                    else:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation",
                                 "IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (
                            uid(), d, str(emp.id), str(dm.wsid),
                            timedelta(hours=dm.start.hour, minutes=dm.start.minute),
                            timedelta(hours=dm.end.hour, minutes=dm.end.minute),
                            calc_obs(emp, dm, ass, fixed_ids),
                            False, now()
                        ))
            c.commit()
    except Exception as e:
        return jsonify({"error": "Error al guardar", "detail": str(e)}), 500

    message = "Horario guardado (flexible, UserShift exacto/bloqueo)" if flexible else "Horario guardado (estricto, UserShift exacto/bloqueo)"
    return jsonify({"message": message, **res}), 201

@app.route('/api/agenda/diagnostics')
def diagnostics():
    wk = request.args.get('week_start')
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    try:
        emps, demands, tpl, week, fixed, shift_types, exact_matches = load_data(ws)

        workstation_analysis = defaultdict(lambda: {
            'total_demand': 0,
            'available_employees': 0,
            'employee_names': [],
            'max_theoretical_coverage': 0,
            'issues': []
        })

        for d in demands:
            workstation_analysis[d.wsname]['total_demand'] += d.need

        for emp in emps:
            for ws_id in emp.roles:
                ws_name = next((x.wsname for x in demands if x.wsid == ws_id), None)
                if ws_name:
                    workstation_analysis[ws_name]['available_employees'] += 1
                    workstation_analysis[ws_name]['employee_names'].append(emp.name)

        for ws_name, data in workstation_analysis.items():
            max_cov = data['available_employees'] * 12  # heurística
            data['max_theoretical_coverage'] = min(max_cov, data['total_demand'])
            coverage_pct = (data['max_theoretical_coverage'] / data['total_demand'] * 100) if data['total_demand'] > 0 else 100
            if coverage_pct < 50:
                data['issues'].append(f"Critico: {coverage_pct:.1f}% posible")
            elif coverage_pct < 80:
                data['issues'].append(f"Advertencia: {coverage_pct:.1f}% posible")
            if data['available_employees'] == 0:
                data['issues'].append("Sin empleados capacitados")

        return jsonify({
            "template": tpl,
            "week_start": ws.isoformat(),
            "analysis": dict(workstation_analysis),
            "usershift_exact_matches": {f"{k[0]}|{k[1].isoformat()}": v for k, v in exact_matches.items()}
        }), 200

    except Exception as e:
        return jsonify({"error": str(e)}), 500

@app.route('/api/agenda/comparison')
def comparison():
    wk = request.args.get('week_start')
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    try:
        strict_result = None
        strict_error = None
        try:
            strict_result, _, _, _, _ = generate(ws)
        except Exception as e:
            strict_error = str(e)

        flexible_result = None
        flexible_error = None
        try:
            flexible_result, _, _, _, _ = generate_flexible(ws)
        except Exception as e:
            flexible_error = str(e)

        return jsonify({
            "week_start": ws.isoformat(),
            "strict_mode": {
                "success": strict_result is not None,
                "error": strict_error,
                "result": strict_result
            },
            "flexible_mode": {
                "success": flexible_result is not None,
                "error": flexible_error,
                "result": flexible_result
            },
            "recommendation": (
                "Usar modo flexible" if strict_error and not flexible_error
                else "Ambos modos funcionan (UserShift exacto/bloqueo)"
                if not strict_error and not flexible_error
                else "Revisar configuración - ambos modos fallan"
            )
        }), 200

    except Exception as e:
        return jsonify({"error": str(e)}), 500

# ───────── MAIN ─────────
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")

if __name__ == "__main__":
    print("API Gandarias v4.0 en http://localhost:5000")
    print("UserShifts: EXACTOS y BLOQUEO si no hay match; ≥1 obligatorio cuando sí hay match.")
    app.run(host="0.0.0.0", port=5000, debug=True)
