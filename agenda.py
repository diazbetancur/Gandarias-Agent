#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGENDA GENERATOR API – Gandarías v3.6   (31-jul-2025)

• Selección de plantilla:
    1) Primero por rango de fechas (StartDate/EndDate) que se solape con la semana pedida
    2) Si no existe, usar la única plantilla con IsActive = TRUE
• Turnos obligatorios (UserShifts) → prioridad, sin BT/C.
• VAC / ABS visibles en preview y guardados en BD (Workstation “AUSENCIA”).
"""

import uuid
import logging
import psycopg2
from datetime import datetime, date, time, timedelta, timezone
from collections import defaultdict
from typing import List, Tuple

from ortools.sat.python import cp_model
from flask import Flask, request, jsonify
from flask_cors import CORS
from psycopg2 import OperationalError, DataError, ProgrammingError

# ───────── FLASK APP ─────────
app = Flask(__name__)
CORS(app)

# ───────── BD CONFIG ─────────
DB = {
    "host":     "gandarias-db.postgres.database.azure.com",
    "port":     5432,
    "dbname":   "postgres",
    "user":     "Admingandarias",
    "password": "Gandarias1.",
    "sslmode":  "require",
}

ABS_WS_ID = '00000000-0000-0000-0000-000000000000'   # Puesto AUSENCIA

# ───────── PARÁMETROS ─────────
MIN_HOURS_BETWEEN_SHIFTS = 9
MIN_HOURS_BETWEEN_SPLIT  = 4
MAX_SHIFTS_CONTINUOUS    = 1
MAX_SHIFTS_SPLIT         = 2
MAX_SHIFTS_HYBRID        = 4
MAX_DAYS_PER_WEEK        = 6

uid = lambda: str(uuid.uuid4())
now = lambda: datetime.now(timezone.utc)

# ───────── EXCEPCIONES ─────────
class DatabaseConnectionError(Exception): ...
class DataNotFoundError(Exception): ...
class DataIntegrityError(Exception): ...
class ScheduleGenerationError(Exception): ...

# ───────── MODELOS ─────────
class Emp:
    def __init__(self, row: Tuple):
        self.id, self.name, self.split = row
        self.roles   = set()
        self.day_off = set()
        self.window  = defaultdict(list)
        self.exc     = defaultdict(list)
        self.absent  = set()
        self.abs_reason = {}      # fecha → 'VAC' / 'ABS'

    def is_hybrid(self):      return len(self.roles) >= 4
    def can(self, ws):        return ws in self.roles
    def off(self, d):         return d.weekday() in self.day_off
    def absent_day(self, d):  return d in self.absent

    def available(self, d, s, e):
        if self.off(d) or self.absent_day(d): return False
        win = self.exc.get(d) or self.window.get(d.weekday(), [(time(0), time(23,59))])
        return any(a <= s and e <= b for a, b in win)

class Demand:
    def __init__(self, row: Tuple):
        (self.id, rdate, self.wsid, self.wsname,
         self.start, self.end, need) = row
        self.date = rdate.date() if hasattr(rdate, 'date') else rdate
        self.need = int(need)

# ───────── HELPERS BD ─────────
def conn():
    try:
        return psycopg2.connect(**DB)
    except OperationalError as e:
        t = str(e)
        if "could not connect" in t:      raise DatabaseConnectionError("No se puede conectar al servidor de BD")
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

def pick_template(cur, week_start: date, week_end: date):
    """Primero intenta por rango StartDate/EndDate; si no, cae a la plantilla activa única."""
    # 1) Por rango (solapamiento con la semana)
    rows = fetchall(cur, '''
        SELECT "Id","Name"
        FROM "Management"."WorkstationDemandTemplates"
        WHERE COALESCE("StartDate", '-infinity'::date) <= %s
          AND COALESCE("EndDate",   'infinity'::date)   >= %s
        ORDER BY COALESCE("StartDate", '-infinity'::date) DESC,
                 COALESCE("DateCreated", '-infinity'::timestamptz) DESC
        LIMIT 1
    ''', (week_end, week_start))
    if rows:
        return rows[0]

    # 2) Por activo único
    cur.execute('SELECT "Id","Name" FROM "Management"."WorkstationDemandTemplates" WHERE "IsActive"')
    act = cur.fetchall()
    if not act:
        raise DataNotFoundError("No existe plantilla por rango ni plantilla activa")
    if len(act) > 1:
        raise DataIntegrityError("Existen múltiples plantillas activas; deja sólo una activa")
    return act[0]

# ───────── CARGA DATOS ─────────
def load_data(week_start: date):
    week = [week_start + timedelta(days=i) for i in range(7)]
    week_end = week[-1]

    with conn() as c, c.cursor() as cur:
        tpl_id, tpl_name = pick_template(cur, week_start, week_end)

        # Demandas
        demands = [Demand(r) for r in fetchall(cur, '''
            SELECT d."Id", %s + d."Day"*interval '1 day',
                   d."WorkstationId", w."Name",
                   (TIMESTAMP '2000-01-01'+d."StartTime")::time,
                   (TIMESTAMP '2000-01-01'+d."EndTime")::time,
                   d."EffortRequired"
            FROM "Management"."WorkstationDemands" d
            JOIN "Management"."Workstations"       w ON w."Id" = d."WorkstationId"
            WHERE d."TemplateId" = %s
              AND w."IsActive" AND NOT w."IsDeleted"
            ORDER BY d."Day", d."StartTime"
        ''', (week_start, tpl_id))]
        if not demands:
            raise DataNotFoundError("La plantilla seleccionada no tiene demandas")

        # Empleados
        emps = {r[0]: Emp(r) for r in fetchall(cur, '''
            SELECT "Id",
                   COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                   COALESCE("ComplementHours", TRUE)
            FROM "Management"."AspNetUsers"
            WHERE "IsActive" AND NOT "IsDelete"
        ''')}
        if not emps:
            raise DataNotFoundError("No hay empleados activos")

        # Roles
        for uid, ws in fetchall(cur, '''
            SELECT "UserId","WorkstationId"
            FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete"
        '''):
            if uid in emps:
                emps[uid].roles.add(ws)
        if not any(e.roles for e in emps.values()):
            raise DataNotFoundError("Ningún empleado tiene roles asignados")

        # Restricciones semanales
        for uid,dow,rt,f,t in fetchall(cur, '''
            SELECT "UserId","DayOfWeek","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleRestrictions"
        '''):
            if uid not in emps: continue
            if rt == 0:
                emps[uid].day_off.add(dow)
            elif f and t:
                emps[uid].window[dow].append(((datetime.min + f).time(),
                                              (datetime.min + t).time()))

        # Restricciones exactas
        for uid,d,rt,f,t in fetchall(cur, '''
            SELECT "UserId","Date","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s
        ''', (week_start, week_end)):
            if uid not in emps: continue
            if rt == 0:
                emps[uid].absent.add(d)
            elif f and t:
                emps[uid].exc[d].append(((datetime.min + f).time(),
                                         (datetime.min + t).time()))

        # Licencias → VAC
        for uid,sd,ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date,
                   COALESCE("EndDate"::date,%s)
            FROM "Management"."Licenses"
            WHERE "StartDate"::date <= %s
              AND COALESCE("EndDate"::date,%s) >= %s
        ''', (week_end, week_end, week_end, week_start)):
            if uid not in emps: continue
            d = max(sd, week_start)
            while d <= ed:
                emps[uid].absent.add(d); emps[uid].abs_reason[d] = 'VAC'
                d += timedelta(days=1)

        # Ausentismos → ABS
        for uid,sd,ed in fetchall(cur, '''
            SELECT "UserId","StartDate"::date,
                   COALESCE("EndDate"::date,%s)
            FROM "Management"."UserAbsenteeisms"
            WHERE "StartDate"::date <= %s
              AND COALESCE("EndDate"::date,%s) >= %s
        ''', (week_end, week_end, week_end, week_start)):
            if uid not in emps: continue
            d = max(sd, week_start)
            while d <= ed:
                emps[uid].absent.add(d); emps[uid].abs_reason[d] = 'ABS'
                d += timedelta(days=1)

        # Turnos obligatorios (UserShifts) — prioridad
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
                if blk is None: continue
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
def overlap(a,b): return not (a.end<=b.start or b.end<=a.start)

def solve(emps: List[Emp], dem: List[Demand], week: List[date]):
    mdl = cp_model.CpModel(); X = {}
    for d in dem:
        for e in emps:
            if e.can(d.wsid) and e.available(d.date, d.start, d.end):
                X[e.id,d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if not X: raise ScheduleGenerationError("Sin variables: nadie puede cubrir demandas")

    # cubrir demanda
    for d in dem:
        mdl.Add(sum(X[e.id,d.id] for e in emps if (e.id,d.id) in X) == d.need)

    # no solapamiento
    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    for lst in by_day.values():
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id,lst[i].id) in X and (e.id,lst[j].id) in X:
                            mdl.Add(X[e.id,lst[i].id] + X[e.id,lst[j].id] <= 1)

    # límites/día
    for e in emps:
        for d in week:
            vs = [X[e.id,dm.id] for dm in dem if dm.date == d and (e.id,dm.id) in X]
            if vs:
                maxs = MAX_SHIFTS_HYBRID if e.is_hybrid() else MAX_SHIFTS_SPLIT if e.split else MAX_SHIFTS_CONTINUOUS
                mdl.Add(sum(vs) <= maxs)

    # máx días/sem
    for e in emps:
        mdl.Add(sum(X[e.id,d.id] for d in dem if (e.id,d.id) in X) <= MAX_DAYS_PER_WEEK)

    # descanso ≥9h
    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id,a.id) in X and (e.id,b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id,a.id] + X[e.id,b.id] <= 1)

    # bloques partidos ≥4h
    for e in emps:
        if not e.split: continue
        for d in by_day:
            lst = [dm for dm in dem if dm.date == d]
            for i in range(len(lst)):
                for j in range(i+1, len(lst)):
                    a,b = lst[i], lst[j]
                    if (e.id,a.id) in X and (e.id,b.id) in X and not overlap(a,b):
                        if 0 < (to_min(b.start)-to_min(a.end))/60 < MIN_HOURS_BETWEEN_SPLIT:
                            mdl.Add(X[e.id,a.id] + X[e.id,b.id] <= 1)

    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = 120
    if sol.Solve(mdl) not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ScheduleGenerationError("Modelo sin solución")

    out = defaultdict(list)
    for d in dem:
        for e in emps:
            if (e.id,d.id) in X and sol.Value(X[e.id,d.id]):
                out[d.date].append((e,d))
    return out

# ───────── OBSERVACIONES ─────────
def calc_obs(emp: Emp, d: date, assigns: list, fixed_ids: set):
    for e, dm in assigns:
        if e.id == emp.id and (e.id, dm.id) in fixed_ids:
            return ""          # turno fijo jamás lleva BT/C
    cnt = sum(1 for e, _ in assigns if e.id == emp.id)
    if cnt == 1: return ""
    maxs = MAX_SHIFTS_HYBRID if emp.is_hybrid() else \
           MAX_SHIFTS_SPLIT  if emp.split      else MAX_SHIFTS_CONTINUOUS
    return "BT" if cnt < maxs else "C"

# ───────── GENERAR HORARIO ─────────
def generate(week_start: date):
    emps, demands, tpl, week, fixed = load_data(week_start)
    sched = solve(emps, demands, week)
    for d, lst in fixed.items():
        sched[d].extend(lst)

    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    # Añadir ausencias/licencias al preview
    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id":   uid(),
                    "wsid": ABS_WS_ID,
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
            "coverage": round(total_ass/total_req*100, 1) if total_req else 0
        },
        "schedule": {}
    }

    for d in week:
        k = d.isoformat()
        res["schedule"][k] = []
        for emp, dm in sched.get(d, []):
            res["schedule"][k].append({
                "employee_id":   str(emp.id),
                "employee_name": emp.name,
                "workstation_id":  str(dm.wsid),
                "workstation_name":dm.wsname,
                "start_time":    "--" if dm.wsid == ABS_WS_ID else dm.start.strftime("%H:%M"),
                "end_time":      "--" if dm.wsid == ABS_WS_ID else dm.end.strftime("%H:%M"),
                "observation":   "VAC" if dm.wsid == ABS_WS_ID and emp.abs_reason.get(d) == "VAC"
                                 else "ABS" if dm.wsid == ABS_WS_ID
                                 else calc_obs(emp, d, sched[d], fixed_ids)
            })

    return res, sched, emps, week, fixed_ids

# ───────── ENDPOINTS ─────────
@app.route('/api/health')
def health():
    st = {"status":"checking","timestamp":now().isoformat(),"version":"3.6","checks":{}}
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute("SELECT version()")
            st["checks"]["database"] = {"status":"healthy","version":cur.fetchone()[0].split(',')[0]}
            st["status"]="healthy"
    except Exception as e:
        st["checks"]["database"] = {"status":"unhealthy","message":str(e)}
        st["status"]="unhealthy"
    return jsonify(st), 200 if st["status"]=="healthy" else 503

@app.route('/api/agenda/preview')
def preview():
    wk = request.args.get('week_start')
    if not wk: return jsonify({"error":"Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error":"Fecha inválida"}), 400
    try:
        res, _, _, _, _ = generate(ws)
        return jsonify(res), 200
    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
        return jsonify({"error": str(e)}), 400

@app.route('/api/agenda/save', methods=['POST'])
def save():
    data  = request.get_json() or {}
    wk    = data.get('week_start')
    force = data.get('force', False)
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400
    we = ws + timedelta(days=6)

    try:
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
                cur.execute('DELETE FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s', (ws, we))

            # insertar filas
            for d, ass in sched.items():
                for emp, dm in ass:
                    if dm.wsid == ABS_WS_ID:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation",
                                 "IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (uid(), d, str(emp.id), ABS_WS_ID,
                              None, None, emp.abs_reason.get(d, 'ABS'),
                              False, now()))
                    else:
                        cur.execute('''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation",
                                 "IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                        ''', (uid(), d, str(emp.id), str(dm.wsid),
                              timedelta(hours=dm.start.hour, minutes=dm.start.minute),
                              timedelta(hours=dm.end.hour,   minutes=dm.end.minute),
                              calc_obs(emp, d, ass, fixed_ids),
                              False, now()))
            c.commit()
    except Exception as e:
        return jsonify({"error": "Error al guardar", "detail": str(e)}), 500

    return jsonify({"message": "Horario guardado", **res}), 201

# ───────── MAIN ─────────
logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s - %(levelname)s - %(message)s")
if __name__ == "__main__":
    print("🚀 API Gandarías v3.6 ↗ http://localhost:5000")
    app.run(host="0.0.0.0", port=5000, debug=True)
