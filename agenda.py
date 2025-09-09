#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGENDA GENERATOR API – Gandarías v3.7   (21-ago-2025)

• Selección de plantilla:
    1) Primero por rango de fechas (StartDate/EndDate) que se solape con la semana pedida
    2) Si no existe, usar la única plantilla con IsActive = TRUE
• Turnos obligatorios (UserShifts) → prioridad, sin BT/C.
• VAC / ABS visibles en preview y guardados en BD (Workstation "AUSENCIA").
• NUEVO: Solver flexible que permite cobertura parcial cuando no hay suficientes empleados.
• ACTUALIZADO:
    - Máximo de 2 BLOQUES por día (un bloque = tiempo continuo; tramos contiguos cuentan como 1)
    - 9 h/día estrictas en modo estricto; flexibles (penalizadas) en modo flexible
    - Cálculo de BT/C basado en cantidad de BLOQUES del día por empleado
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

# ───────── PARÁMETROS ─────────
MIN_HOURS_BETWEEN_SHIFTS = 9
MIN_HOURS_BETWEEN_SPLIT = 4
MAX_SHIFTS_CONTINUOUS = 1   # (ya no se usa para límite/día; se deja por compatibilidad)
MAX_SHIFTS_SPLIT = 2        # (ya no se usa para límite/día; se deja por compatibilidad)
MAX_SHIFTS_HYBRID = 4       # (puede usarse en preferencias/diagnósticos)
MAX_DAYS_PER_WEEK = 6
MAX_HOURS_PER_DAY = 9

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
        self.day_off = set()
        self.window = defaultdict(list)
        self.exc = defaultdict(list)
        self.absent = set()
        self.abs_reason = {}      # fecha → 'VAC' / 'ABS'

    def is_hybrid(self): return len(self.roles) >= 4
    def can(self, ws): return ws in self.roles
    def off(self, d): return d.weekday() in self.day_off
    def absent_day(self, d): return d in self.absent

    def available(self, d, s, e):
        if self.off(d) or self.absent_day(d):
            return False
        win = self.exc.get(d) or self.window.get(
            d.weekday(), [(time(0), time(23, 59))])
        return any(a <= s and e <= b for a, b in win)

class Demand:
    def __init__(self, row: Tuple):
        (self.id, rdate, self.wsid, self.wsname,
         self.start, self.end, need) = row
        self.date = rdate.date() if hasattr(rdate, 'date') else rdate
        self.need = int(need)

# ───────── HELPERS ─────────
def _t2m(t: time) -> int:
    return t.hour * 60 + t.minute

def duration_min(dm) -> int:
    start = _t2m(dm.start)
    end = _t2m(dm.end)
    if dm.end == time(0, 0):
        end = 24*60
    if end < start:              # cruza medianoche
        end += 24*60
    return end - start

def demand_weight(dm) -> int:
    """
    Pondera la importancia de cubrir una demanda.
    Penaliza más dejar vacíos tramos cortos (micro-turnos).
    """
    dur = max(1, duration_min(dm))  # minutos
    return max(1, 60000 // dur)     # Ej: 30min=2000, 60min=1000, 180min=333

# Alias por compatibilidad (si quedaba alguna referencia antigua)
dur_min = duration_min

def _m2t(m: int) -> time:
    return time(m // 60, m % 60)

MAX_SHIFT_DURATION_HOURS = 9

def coalesce_demands(demands, tolerate_gap_min: int = 0):
    """
    Une demandas contiguas del mismo día/puesto cuando
    no hay hueco (o el hueco <= tolerate_gap_min) y el 'need' es igual,
    sin exceder 9 horas continuas por tramo unido.
    """
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
            potential_duration_min = _t2m(nxt.end) - _t2m(curr.start)
            potential_duration_hours = potential_duration_min / 60.0
            if (nxt.need == curr.need
                and _t2m(nxt.start) - _t2m(curr.end) <= tolerate_gap_min
                and potential_duration_hours <= MAX_SHIFT_DURATION_HOURS):
                curr.end = nxt.end
            else:
                merged.append(curr)
                curr = nxt
        merged.append(curr)

    out = []
    for d in merged:
        out.append(Demand((
            d.id, d.date, d.wsid, d.wsname, d.start, d.end, d.need
        )))
    return out

# ───────── UTILIDADES BLOQUES ─────────
def merge_intervals(intervals):
    """ intervals: [(start_min, end_min), ...] -> fusiona por solape o contigüidad (end == next.start se considera continuo). """
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:  # solapa o toca
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def to_min_t(t: time) -> int:
    return t.hour * 60 + t.minute

def count_blocks_for_employee_day(assigns_day_emp):
    """
    assigns_day_emp: lista de Demand para un empleado en un día (solo asignados)
    Devuelve el número de bloques continuos, tratando intervalos contiguos como 1 solo bloque.
    """
    intervals = []
    for dm in assigns_day_emp:
        s = to_min_t(dm.start)
        e = to_min_t(dm.end) if dm.end != time(0,0) else 24*60
        if e < s:  # por seguridad
            e += 24*60
        intervals.append((s, e))
    return len(merge_intervals(intervals))

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
    """
    Selección de plantilla (ignorando el año en Start/End) priorizando cercanía y con demandas > 0.
    """
    print(f"\n{'='*60}")
    print(f"[PICK_TEMPLATE] Buscando plantilla para semana {week_start} a {week_end}")
    print(f"[PICK_TEMPLATE] Mes solicitado: {week_start.month} ({week_start.strftime('%B')})")
    print(f"{'='*60}")

    act = fetchall(cur, '''
        SELECT "Id","Name"
        FROM "Management"."WorkstationDemandTemplates"
        WHERE "IsActive" = TRUE
    ''')
    if len(act) == 1:
        print(f"✓ ENCONTRADA plantilla activa: '{act[0][1]}'")
        return act[0]
    elif len(act) > 1:
        raise DataIntegrityError(f"Hay {len(act)} plantillas activas; debe haber solo una")
    else:
        print("  No hay plantillas activas, continuando por cercanía...")

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

    def md(d: date) -> tuple[int, int]:
        return d.month, d.day

    def same_year(year: int, m: int, d: int) -> date:
        try:
            return date(year, m, d)
        except ValueError:
            return date(year, 2, 28) if (m == 2 and d == 29) else date(year, m, d)

    week_center = week_start + (week_end - week_start) // 2

    def distance_metrics(start_md: tuple[int, int], end_md: tuple[int, int]) -> tuple[int, int]:
        y = week_start.year
        s = same_year(y, start_md[0], start_md[1])
        e = same_year(y, end_md[0],   end_md[1])

        segments = []
        if s <= e:
            segments.append((s, e))
        else:
            segments.append((s, date(y, 12, 31)))
            segments.append((date(y, 1, 1), e))

        def seg_dist(a: date, b: date):
            if not (b < week_start or a > week_end):
                return 0, 0
            if b < week_start:
                d1 = (week_start - b).days
                d2 = abs((week_center - b).days)
            else:
                d1 = (a - week_end).days
                d2 = abs((a - week_center).days)
            return d1, d2

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

    print("\n[PICK_TEMPLATE] Ranking por cercanía (top 5):")
    for i, r in enumerate(scored[:5], 1):
        print(f"  {i:>2}. {r['name']:<24}  dist={r['dist']:>2}  dcenter={r['dcenter']:>2}  demandas={r['demandas']}  ({r['start']}..{r['end']})")

    chosen = next((r for r in scored if r["demandas"] > 0), None)
    if chosen:
        print(f"\n✓ ENCONTRADA por cercanía con demandas: '{chosen['name']}'")
        print(f"  Rango: {chosen['start']} a {chosen['end']} | demandas={chosen['demandas']} | dist={chosen['dist']} dcenter={chosen['dcenter']}")
        return (chosen["id"], chosen["name"])

    print("\n[PICK_TEMPLATE] ✗ Ninguna candidata cercana tiene demandas > 0")
    raise DataNotFoundError("No se encontró ninguna plantilla con demandas > 0")

# ───────── CARGA DATOS ─────────
def load_data(week_start: date):
    week = [week_start + timedelta(days=i) for i in range(7)]
    week_end = week[-1]

    with conn() as c, c.cursor() as cur:
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
        if not demands:
            raise DataNotFoundError("La plantilla seleccionada no tiene demandas")

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

        for uid, dow, rt, f, t in fetchall(cur, '''
            SELECT "UserId","DayOfWeek","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleRestrictions"
        '''):
            if uid not in emps:
                continue
            if rt == 0:
                emps[uid].day_off.add(dow)
            elif f and t:
                emps[uid].window[dow].append(((datetime.min + f).time(),
                                              (datetime.min + t).time()))

        for uid, d, rt, f, t in fetchall(cur, '''
            SELECT "UserId","Date","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s
        ''', (week_start, week_end)):
            if uid not in emps:
                continue
            if rt == 0:
                emps[uid].absent.add(d)
            elif f and t:
                emps[uid].exc[d].append(((datetime.min + f).time(),
                                         (datetime.min + t).time()))

        for uid, sd, ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date,
                   COALESCE("EndDate"::date,%s)
            FROM "Management"."Licenses"
            WHERE "StartDate"::date <= %s
              AND COALESCE("EndDate"::date,%s) >= %s
        ''', (week_end, week_end, week_end, week_start)):
            if uid not in emps:
                continue
            d = max(sd, week_start)
            while d <= ed:
                emps[uid].absent.add(d)
                emps[uid].abs_reason[d] = 'VAC'
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
            d = max(sd, week_start)
            while d <= ed:
                emps[uid].absent.add(d)
                emps[uid].abs_reason[d] = 'ABS'
                d += timedelta(days=1)

        fixed = defaultdict(list)
        for uid, day, blk1, blk2 in fetchall(cur, '''
            SELECT "UserId","Day","Block1Start","Block2Start"
            FROM "Management"."UserShifts"
        '''):
            if uid not in emps:
                continue
            shift_date = week_start + timedelta(days=day)
            if not (week_start <= shift_date <= week_end):
                continue
            for blk in (blk1, blk2):
                if blk is None:
                    continue
                blk_time = (datetime.min + blk).time()
                for dm in demands:
                    if (dm.date == shift_date and dm.start == blk_time and
                        emps[uid].can(dm.wsid) and
                        emps[uid].available(dm.date, dm.start, dm.end) and
                            dm.need > 0):
                        fixed[shift_date].append((emps[uid], dm))
                        dm.need -= 1
                        break
        demands = [d for d in demands if d.need > 0]

    return list(emps.values()), demands, tpl_name, week, fixed

# ───────── SOLVER ─────────
def to_min(t): return t.hour*60+t.minute
def overlap(a, b): return not (a.end <= b.start or b.end <= a.start)

def add_max2_blocks_per_day(mdl, emps, dem, X):
    """
    Impone que cada empleado no pueda tener 3 bloques disjuntos en un mismo día:
    Para cada triple (a,b,c) pairwise disjoint → X_e,a + X_e,b + X_e,c <= 2
    Los tramos contiguos se consideran un solo bloque (no son disjoint).
    """
    # Demands por día
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

def solve(emps: List[Emp], dem: List[Demand], week: List[date]):
    """Solver original (estricto) - requiere 100% de cobertura, 9h/día duras, máx 2 bloques/día."""
    mdl = cp_model.CpModel()
    X = {}
    for d in dem:
        for e in emps:
            if e.can(d.wsid) and e.available(d.date, d.start, d.end):
                X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if not X:
        raise ScheduleGenerationError("Sin variables: nadie puede cubrir demandas")

    # cubrir demanda
    for d in dem:
        mdl.Add(sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X) == d.need)

    # no solapamiento
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)
    for lst in by_day.values():
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # 9h/día DURAS + sin límite de "cantidad de turnos", usamos BLOQUES
    for e in emps:
        for d in week:
            todays = [dm for dm in dem if dm.date == d and (e.id, dm.id) in X]
            if todays:
                mdl.Add(sum(duration_min(dm) * X[e.id, dm.id] for dm in todays) <= MAX_HOURS_PER_DAY * 60)

    # máx días/sem
    for e in emps:
        mdl.Add(sum(X[e.id, d.id] for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)

    # descanso ≥9h entre días
    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id, a.id) in X and (e.id, b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    # bloques partidos ≥4h (si no split no permite gaps cortos)
    for e in emps:
        if not e.split:
            continue
        for dday in by_day:
            lst = [dm for dm in dem if dm.date == dday]
            for i in range(len(lst)):
                for j in range(i+1, len(lst)):
                    a, b = lst[i], lst[j]
                    if (e.id, a.id) in X and (e.id, b.id) in X and not overlap(a, b):
                        if 0 < (to_min(b.start)-to_min(a.end))/60 < MIN_HOURS_BETWEEN_SPLIT:
                            mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    # Máximo 2 bloques/día (DURO)
    add_max2_blocks_per_day(mdl, emps, dem, X)

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

def solve_flexible(emps: List[Emp], dem: List[Demand], week: List[date]):
    """
    Solver flexible que permite cobertura parcial cuando no hay suficientes empleados.
    9h/día se tratan como soft-constraint (overtime penalizado). Máx 2 bloques/día es DURO.
    """
    mdl = cp_model.CpModel()
    X = {}

    for d in dem:
        for e in emps:
            if e.can(d.wsid) and e.available(d.date, d.start, d.end):
                X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")

    if not X:
        raise ScheduleGenerationError("Sin variables: nadie puede cubrir demandas")

    unmet_demand = {d.id: mdl.NewIntVar(0, d.need, f"unmet_{d.id}") for d in dem}

    for d in dem:
        covered = sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X)
        mdl.Add(covered + unmet_demand[d.id] == d.need)

    # No solapamiento
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)
    for lst in by_day.values():
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # 9h/día FLEX: overtime penalizado en el objetivo
    for e in emps:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                total_min_today = sum(duration_min(dm) * X[e.id, dm.id] for dm in todays)
                ot = mdl.NewIntVar(0, 24*60, f"ot_{e.id}_{dday.isoformat()}")
                mdl.Add(ot >= total_min_today - MAX_HOURS_PER_DAY * 60)
                mdl.Add(ot >= 0)
                if not hasattr(mdl, "_overtimes"):
                    mdl._overtimes = []
                mdl._overtimes.append(ot)

    # Máximo días/sem
    for e in emps:
        mdl.Add(sum(X[e.id, d.id] for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)

    # Descanso ≥9h entre días
    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id, a.id) in X and (e.id, b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    # Bloques partidos ≥4h
    for e in emps:
        if not e.split:
            continue
        for dday in by_day:
            lst = [dm for dm in dem if dm.date == dday]
            for i in range(len(lst)):
                for j in range(i+1, len(lst)):
                    a, b = lst[i], lst[j]
                    if (e.id, a.id) in X and (e.id, b.id) in X and not overlap(a, b):
                        if 0 < (to_min(b.start)-to_min(a.end))/60 < MIN_HOURS_BETWEEN_SPLIT:
                            mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    # Máximo 2 bloques/día (DURO en flexible también)
    add_max2_blocks_per_day(mdl, emps, dem, X)

    # 🎯 OBJETIVO: Minimizar demanda no cubierta (ponderada y por minutos) + penalizar overtime
    weights = {d.id: demand_weight(d) for d in dem}
    total_unmet_weighted = sum(weights[d.id] * unmet_demand[d.id] for d in dem)
    total_unmet_minutes  = sum(duration_min(d) * unmet_demand[d.id] for d in dem)
    total_overtime       = sum(mdl._overtimes) if hasattr(mdl, "_overtimes") else 0

    # Prioridades: 1) unmet ponderado  2) minutos unmet  3) overtime
    mdl.Minimize(total_unmet_weighted * 1000 + total_unmet_minutes * 1 + total_overtime * 5)

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

    print(f"\n{'='*80}")
    print(f"📊 REPORTE DE COBERTURA")
    print(f"{'='*80}")
    total_demand = sum(d.need for d in dem)
    total_covered = sum(stats['covered'] for stats in coverage_stats.values())
    total_unmet = sum(stats['unmet'] for stats in coverage_stats.values())
    overall_coverage = round((total_covered / total_demand) * 100, 1) if total_demand > 0 else 100
    print(f"📈 RESUMEN GENERAL:")
    print(f"   Total demandado: {total_demand:,} turnos")
    print(f"   Total cubierto:  {total_covered:,} turnos ({overall_coverage}%)")
    print(f"   Sin cubrir:      {total_unmet:,} turnos")

    critical_issues = [stats for stats in coverage_stats.values() if stats['coverage_pct'] < 50]
    if critical_issues:
        print(f"\n⚠️  TURNOS CON COBERTURA CRÍTICA (<50%):")
        for stats in critical_issues:
            d = stats['demand']
            print(f"   📅 {d.date} {d.start}-{d.end} {d.wsname}: {stats['covered']}/{d.need} ({stats['coverage_pct']}%)")

    by_workstation = defaultdict(lambda: {'demand': 0, 'covered': 0})
    for stats in coverage_stats.values():
        d = stats['demand']
        by_workstation[d.wsname]['demand'] += d.need
        by_workstation[d.wsname]['covered'] += stats['covered']

    print(f"\n📋 COBERTURA POR PUESTO:")
    for ws_name, data in sorted(by_workstation.items()):
        pct = round((data['covered'] / data['demand']) * 100, 1) if data['demand'] > 0 else 100
        status_icon = "🟢" if pct >= 80 else "🟡" if pct >= 50 else "🔴"
        print(f"   {status_icon} {ws_name}: {data['covered']}/{data['demand']} ({pct}%)")
    print(f"{'='*80}\n")

    return out, coverage_stats

# ───────── OBSERVACIONES ─────────
def calc_obs(emp: Emp, dm: Demand, assigns_day: list, fixed_ids: set):
    """
    Observación basada en BLOQUES del día:
      - "C" si el empleado ya está en 2+ bloques (no puede tomar más).
      - "BT" si aún está en <2 bloques (puede tomar más).
    AUSENCIAS siguen como "VAC" / "ABS" y no cuentan para bloques.
    """
    if (emp.id, dm.id) in fixed_ids:
        return ""

    # Demandas reales de ese día para este empleado (sin AUSENCIA)
    todays_emp_dms = [d for e, d in assigns_day if e.id == emp.id and d.wsid is not None]
    blocks = count_blocks_for_employee_day(todays_emp_dms)

    if blocks >= 2:
        return "C"
    else:
        return "BT"

# ───────── GENERATE ─────────
def generate(week_start: date):
    emps, demands, tpl, week, fixed = load_data(week_start)
    sched = solve(emps, demands, week)
    for d, lst in fixed.items():
        sched[d].extend(lst)

    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id":   uid(),
                    "wsid": None,
                    "wsname": "AUSENCIA",
                    "start": time(0, 0),
                    "end":   time(0, 0),
                    "date":  d
                })()
                sched[d].append((emp, pseudo_dm))

    total_req = sum(dm.need for dm in demands) + len(fixed_ids)
    total_ass = sum(len(v) for v in sched.values())

    res = {
        "template": tpl,
        "week_start": week_start.isoformat(),
        "week_end":   (week_start + timedelta(days=6)).isoformat(),
        "summary": {
            "total_employees": len(emps),
            "total_demands":   total_req,
            "total_assignments": total_ass,
            "coverage": round(total_ass/total_req*100, 1) if total_req else 0,
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

def generate_flexible(week_start: date):
    emps, demands, tpl, week, fixed = load_data(week_start)
    sched, coverage_stats = solve_flexible(emps, demands, week)
    for d, lst in fixed.items():
        sched[d].extend(lst)

    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id": uid(),
                    "wsid": None,
                    "wsname": "AUSENCIA",
                    "start": time(0, 0),
                    "end": time(0, 0),
                    "date": d
                })()
                sched[d].append((emp, pseudo_dm))

    total_req = sum(dm.need for dm in demands) + len(fixed_ids)
    total_covered = sum(stats['covered'] for stats in coverage_stats.values()) + len(fixed_ids)
    total_ass = sum(len(v) for v in sched.values())

    res = {
        "template": tpl,
        "week_start": week_start.isoformat(),
        "week_end": (week_start + timedelta(days=6)).isoformat(),
        "summary": {
            "total_employees": len(emps),
            "total_demands": total_req,
            "total_covered": total_covered,
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
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "workstation_id": (str(dm.wsid) if dm.wsid is not None else None),
                "workstation_name": dm.wsname,
                "start_time": (dm.start.strftime("%H:%M") if dm.start else None),
                "end_time": (dm.end.strftime("%H:%M") if dm.end else None),
                "observation": (
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
          "version": "3.7", "checks": {}}
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

    message = "Horario guardado con cobertura flexible" if flexible else "Horario guardado"
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
        emps, demands, tpl, week, fixed = load_data(ws)

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
                ws_name = next((d.wsname for d in demands if d.wsid == ws_id), None)
                if ws_name:
                    workstation_analysis[ws_name]['available_employees'] += 1
                    workstation_analysis[ws_name]['employee_names'].append(emp.name)

        for ws_name, data in workstation_analysis.items():
            max_coverage = data['available_employees'] * 12  # 6 días * 2 turnos (referencia)
            data['max_theoretical_coverage'] = min(max_coverage, data['total_demand'])
            coverage_pct = (data['max_theoretical_coverage'] / data['total_demand'] * 100) if data['total_demand'] > 0 else 100
            if coverage_pct < 50:
                data['issues'].append(f"CRÍTICO: Solo {coverage_pct:.1f}% de cobertura posible")
            elif coverage_pct < 80:
                data['issues'].append(f"ADVERTENCIA: Solo {coverage_pct:.1f}% de cobertura posible")
            if data['available_employees'] == 0:
                data['issues'].append("Sin empleados capacitados")
            elif data['available_employees'] < 3:
                data['issues'].append(f"Muy pocos empleados ({data['available_employees']})")

        return jsonify({
            "template": tpl,
            "week_start": ws.isoformat(),
            "analysis": dict(workstation_analysis),
            "recommendations": [
                "Usar modo flexible si hay problemas de cobertura",
                "Capacitar más empleados en puestos críticos",
                "Revisar si las demandas son realistas"
            ]
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
                else "Ambos modos funcionan, usar estricto para cobertura completa"
                if not strict_error and not flexible_error
                else "Revisar configuración - ambos modos fallan"
            )
        }), 200

    except Exception as e:
        return jsonify({"error": str(e)}), 500

# ───────── MAIN ─────────
logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s - %(levelname)s - %(message)s")

if __name__ == "__main__":
    print("🚀 API Gandarías v3.7 ↗ http://localhost:5000")
    print("📋 Nuevas funcionalidades:")
    print("   • Solver flexible para cobertura parcial")
    print("   • Máximo 2 bloques por día (continuidad cuenta como 1)")
    print("   • 9h/día duras en estricto, flex en flexible (penalizadas)")
    print("   • Endpoint /api/agenda/diagnostics")
    print("   • Endpoint /api/agenda/comparison")
    print("   • Parámetros flexible=true/false en preview y save")
    app.run(host="0.0.0.0", port=5000, debug=True)
