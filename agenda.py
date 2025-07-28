
"""
AGENDA GENERATOR API – Gandarías v3.1
Endpoints:
• GET  /api/health          → Diagnóstico del sistema
• GET  /api/agenda/preview  → Genera e imprime agenda (week_start obligatorio)
• POST /api/agenda/save     → Genera y guarda agenda (week_start obligatorio)
"""

import uuid, psycopg2, traceback, logging
from datetime import datetime, date, time, timedelta, timezone
from collections import defaultdict
from typing import List, Tuple
from ortools.sat.python import cp_model
from flask import Flask, request, jsonify
from flask_cors import CORS
from psycopg2 import OperationalError, IntegrityError, DataError, ProgrammingError

# ───────── FLASK APP ─────────
app = Flask(__name__)
CORS(app)

# ───────── CONFIG BD ─────────
DB = {
    "host":     "gandarias-db.postgres.database.azure.com",
    "port":     5432,
    "dbname":   "postgres",
    "user":     "Admingandarias",
    "password": "Gandarias1.",
    "sslmode":  "require",
}

# ───────── PARÁMETROS DE NEGOCIO ─────────
MIN_HOURS_BETWEEN_SHIFTS = 9
MIN_HOURS_BETWEEN_SPLIT  = 4
MAX_SHIFTS_CONTINUOUS    = 1
MAX_SHIFTS_SPLIT         = 2
MAX_SHIFTS_HYBRID        = 4
MAX_DAYS_PER_WEEK        = 6

uid = lambda: str(uuid.uuid4())
now = lambda: datetime.now(timezone.utc)

# ───────── EXCEPCIONES ─────────
class DatabaseConnectionError(Exception): pass
class DataNotFoundError(Exception): pass
class DataIntegrityError(Exception): pass
class ScheduleGenerationError(Exception): pass

# ───────── MODELOS ─────────
class Emp:
    def __init__(self, row: Tuple):
        self.id, self.name, self.split = row
        self.roles   = set()
        self.day_off = set()
        self.window  = defaultdict(list)
        self.exc     = defaultdict(list)
        self.absent  = set()

    def is_hybrid(self):          return len(self.roles) >= 4
    def can(self, ws):            return ws in self.roles
    def off(self, d):             return d.weekday() in self.day_off
    def absent_day(self, d):      return d in self.absent
    def available(self, d, s, e):
        if self.off(d) or self.absent_day(d):
            return False
        win = self.exc.get(d) or self.window.get(d.weekday(), [(time(0), time(23,59))])
        return any(w0 <= s and e <= w1 for w0, w1 in win)

class Demand:
    def __init__(self, row: Tuple):
        (self.id, row_date, self.wsid, self.wsname,
         self.start, self.end, need) = row
        self.date = row_date.date() if hasattr(row_date,"date") else row_date
        self.need = int(need)

# ───────── HELPERS BD ─────────
def conn():
    try:
        return psycopg2.connect(**DB)
    except OperationalError as e:
        msg = str(e)
        if "could not connect" in msg: raise DatabaseConnectionError("No se puede conectar al servidor de BD")
        if "authentication failed" in msg: raise DatabaseConnectionError("Credenciales de BD incorrectas")
        raise DatabaseConnectionError(msg)

def fetchall(cur, sql, pars=()):
    try: cur.execute(sql, pars); return cur.fetchall()
    except (ProgrammingError, DataError) as e: raise DataIntegrityError(str(e))

def get_week_start(d: date) -> date:
    while d.weekday() != 0: d -= timedelta(days=1)
    return d

# ───────── CARGA DATOS ─────────
def load_data(week_start: date):
    week_dates=[week_start+timedelta(days=i) for i in range(7)]
    with conn() as c, c.cursor() as cur:
        # Plantilla activa
        tpl = fetchall(cur,
            'SELECT "Id" FROM "Management"."WorkstationDemandTemplates" WHERE "IsActive" LIMIT 1')
        if not tpl: raise DataNotFoundError("No hay plantilla de demanda activa")
        tpl = tpl[0][0]

        # Demandas
        dem_rows = fetchall(cur, '''
            SELECT d."Id",
                   %s + d."Day"*interval '1 day',
                   d."WorkstationId", w."Name",
                   (TIMESTAMP '2000-01-01' + d."StartTime")::time,
                   (TIMESTAMP '2000-01-01' + d."EndTime")::time,
                   d."EffortRequired"
            FROM "Management"."WorkstationDemands" d
            JOIN "Management"."Workstations" w ON w."Id"=d."WorkstationId"
            WHERE d."TemplateId"=%s AND w."IsActive" AND NOT w."IsDeleted"
            ORDER BY d."Day", d."StartTime"
        ''', (week_start, tpl))
        if not dem_rows: raise DataNotFoundError("No se encontraron demandas para la plantilla activa")
        demands=[Demand(r) for r in dem_rows]

        # Empleados
        emp_rows = fetchall(cur, '''
            SELECT "Id", COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                   COALESCE("ComplementHours", TRUE)
            FROM "Management"."AspNetUsers"
            WHERE "IsActive" AND NOT "IsDelete"
        ''')
        if not emp_rows: raise DataNotFoundError("No hay empleados activos")
        emps={r[0]: Emp(r) for r in emp_rows}

        # Roles
        for uid, ws in fetchall(cur, '''
            SELECT "UserId","WorkstationId" FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete"
        '''):
            if uid in emps: emps[uid].roles.add(ws)
        if not any(e.roles for e in emps.values()):
            raise DataNotFoundError("Ningún empleado tiene roles asignados")

        # Restricciones semanales
        for uid,dow,rt,f,t in fetchall(cur,'''
            SELECT "UserId","DayOfWeek","RestrictionType","AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleRestrictions"'''):
            if uid not in emps: continue
            if rt==0: emps[uid].day_off.add(dow)
            elif f and t:
                emps[uid].window[dow].append(((datetime.min+f).time(),
                                              (datetime.min+t).time()))

        # Excepciones exactas
        for uid,d,rt,f,t in fetchall(cur,'''
            SELECT "UserId","Date","RestrictionType","AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s''',(week_start,week_dates[-1])):
            if uid not in emps: continue
            if rt==0: emps[uid].absent.add(d)
            elif f and t:
                emps[uid].exc[d].append(((datetime.min+f).time(),
                                          (datetime.min+t).time()))

        # Ausentismos / licencias
        for tbl in ["UserAbsenteeisms","Licenses"]:
            for uid,sd,ed in fetchall(cur,f'''
                SELECT "UserId","StartDate"::date,COALESCE("EndDate"::date,%s)
                FROM "Management"."{tbl}"
                WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s''',
                (week_dates[-1], week_dates[-1], week_dates[-1], week_start)):
                if uid not in emps: continue
                d=max(sd,week_start)
                while d<=ed:
                    emps[uid].absent.add(d); d+=timedelta(days=1)

    return list(emps.values()), demands

# ───────── OPTIMIZACIÓN ─────────
def time_to_min(t): return t.hour*60+t.minute
def overlap(a,b):   return not (a.end<=b.start or b.end<=a.start)

def solve(emps: List[Emp], dem: List[Demand], week_dates: List[date]):
    mdl=cp_model.CpModel(); X={}
    for d in dem:
        for e in emps:
            if e.can(d.wsid) and e.available(d.date,d.start,d.end):
                X[e.id,d.id]=mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if not X: raise ScheduleGenerationError("Sin variables: nadie puede cubrir demandas")

    # 1 cubrir demanda
    for d in dem: mdl.Add(sum(X[e.id,d.id] for e in emps if (e.id,d.id) in X)==d.need)

    # 2 no solapamiento
    by_day=defaultdict(list)
    for d in dem: by_day[d.date].append(d)
    for day,l in by_day.items():
        for i in range(len(l)):
            for j in range(i+1,len(l)):
                if overlap(l[i],l[j]):
                    for e in emps:
                        if (e.id,l[i].id) in X and (e.id,l[j].id) in X:
                            mdl.Add(X[e.id,l[i].id]+X[e.id,l[j].id]<=1)

    # 3 límites/día
    for e in emps:
        for d in week_dates:
            vs=[X[e.id,dm.id] for dm in dem if dm.date==d and (e.id,dm.id) in X]
            if vs:
                maxs = MAX_SHIFTS_HYBRID if e.is_hybrid() else MAX_SHIFTS_SPLIT if e.split else MAX_SHIFTS_CONTINUOUS
                mdl.Add(sum(vs)<=maxs)

    # 4 máx días/sem
    for e in emps: mdl.Add(sum(X[e.id,d.id] for d in dem if (e.id,d.id) in X) <= MAX_DAYS_PER_WEEK)

    # 5 9h entre jornadas
    for e in emps:
        for t in dem:
            for n in dem:
                if n.date==t.date+timedelta(days=1) and (e.id,t.id) in X and (e.id,n.id) in X:
                    gap=(24*60-time_to_min(t.end))+time_to_min(n.start)
                    if gap<MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id,t.id]+X[e.id,n.id]<=1)

    # 6 4h entre bloques partidos
    for e in emps:
        if not e.split: continue
        for d in by_day:
            lst=[dm for dm in dem if dm.date==d]
            for i in range(len(lst)):
                for j in range(i+1,len(lst)):
                    a,b=lst[i],lst[j]
                    if (e.id,a.id) in X and (e.id,b.id) in X and not overlap(a,b):
                        if 0<(time_to_min(b.start)-time_to_min(a.end))/60<MIN_HOURS_BETWEEN_SPLIT:
                            mdl.Add(X[e.id,a.id]+X[e.id,b.id]<=1)

    sol=cp_model.CpSolver(); sol.parameters.max_time_in_seconds=120
    if sol.Solve(mdl) not in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        raise ScheduleGenerationError("Modelo sin solución")
    out=defaultdict(list)
    for d in dem:
        for e in emps:
            if (e.id,d.id) in X and sol.Value(X[e.id,d.id]):
                out[d.date].append((e,d))
    return out

# ───────── UTILIDADES RESULTADO ─────────
def calc_obs(emp:Emp,d,assigns,all_dem):
    cnt=len([1 for e,_ in assigns if e.id==emp.id])
    maxs = MAX_SHIFTS_HYBRID if emp.is_hybrid() else MAX_SHIFTS_SPLIT if emp.split else MAX_SHIFTS_CONTINUOUS
    return "C" if cnt>=maxs else "BT"

def generate_schedule(week_start: date):
    week_dates=[week_start+timedelta(days=i) for i in range(7)]
    emps,demands=load_data(week_start)
    sched=solve(emps,demands,week_dates)
    res={"week_start":week_start.isoformat(),
         "week_end":(week_start+timedelta(days=6)).isoformat(),
         "schedule":{}, "summary":{}}
    total_req=sum(d.need for d in demands)
    total_ass=sum(len(v) for v in sched.values())
    res["summary"]={"total_employees":len(emps),
                    "total_demands":len(demands),
                    "total_assignments":total_ass,
                    "coverage":round(total_ass/total_req*100,1) if total_req else 0}
    for d in week_dates:
        key=d.isoformat(); res["schedule"][key]=[]
        for emp,dm in sched.get(d,[]):
            res["schedule"][key].append({
                "employee_id":str(emp.id),"employee_name":emp.name,
                "workstation_id":str(dm.wsid),"workstation_name":dm.wsname,
                "start_time":dm.start.strftime("%H:%M"),
                "end_time":dm.end.strftime("%H:%M"),
                "observation":calc_obs(emp,d,sched[d],demands)})
    return res,sched,emps,demands

# ───────── ENDPOINTS ─────────
@app.route('/api/health',methods=['GET'])
def health():
    st={"status":"checking","timestamp":now().isoformat(),"version":"3.1","checks":{}}
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute("SELECT version()")
            st["checks"]["database"]={"status":"healthy","version":cur.fetchone()[0].split(',')[0]}
            st["status"]="healthy"
    except Exception as e:
        st["checks"]["database"]={"status":"unhealthy","message":str(e)}; st["status"]="unhealthy"
    return jsonify(st),200 if st["status"]=="healthy" else 503

@app.route('/api/agenda/preview',methods=['GET'])
def preview():
    wk=request.args.get('week_start')
    if not wk: return jsonify({"error":"Falta week_start"}),400
    try: ws=get_week_start(datetime.strptime(wk,'%Y-%m-%d').date())
    except ValueError: return jsonify({"error":"Fecha inválida"}),400
    try:
        res,_,_,_ = generate_schedule(ws); return jsonify(res),200
    except (DatabaseConnectionError,DataNotFoundError,ScheduleGenerationError) as e:
        return jsonify({"error":str(e)}),400

@app.route('/api/agenda/save',methods=['POST'])
def save():
    data=request.get_json() or {}
    wk=data.get('week_start'); force=data.get('force',False)
    if not wk: return jsonify({"error":"Falta week_start"}),400
    try: ws=get_week_start(datetime.strptime(wk,'%Y-%m-%d').date())
    except ValueError: return jsonify({"error":"Fecha inválida"}),400
    we=ws+timedelta(days=6)

    # 1 ¿Ya hay agenda activa (IsDeleted=FALSE)?
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute('SELECT COUNT(*) FROM "Management"."Schedules" WHERE NOT "IsDeleted"')
            if cur.fetchone()[0]>0:
                return jsonify({"error":"Ya hay una agenda activa",
                                "message":"Elimina o marca como eliminada la agenda vigente antes de guardar una nueva"}),400
    except Exception as e:
        return jsonify({"error":"Error al verificar agendas activas","detail":str(e)}),500

    # 2 generar
    try:
        res,sched,emps,demands=generate_schedule(ws)
    except (DatabaseConnectionError,DataNotFoundError,ScheduleGenerationError) as e:
        return jsonify({"error":str(e)}),400

    # 3 duplicados misma semana
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute('SELECT COUNT(*) FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s',
                        (ws,we)); existing=cur.fetchone()[0]
            if existing and not force:
                return jsonify({"error":"Horario ya existe para esa semana","existing_records":existing}),409
            if existing and force:
                cur.execute('DELETE FROM "Management"."Schedules" WHERE "Date" BETWEEN %s AND %s',(ws,we))
            # insertar
            for d,ass in sched.items():
                for emp,dm in ass:
                    cur.execute('''INSERT INTO "Management"."Schedules"
                                   ("Id","Date","UserId","WorkstationId","StartTime","EndTime",
                                    "Observation","IsDeleted","DateCreated")
                                   VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)''',
                        (uid(),d,str(emp.id),str(dm.wsid),
                         timedelta(hours=dm.start.hour,minutes=dm.start.minute),
                         timedelta(hours=dm.end.hour,minutes=dm.end.minute),
                         calc_obs(emp,d,ass,demands),False,now()))
            c.commit()
    except Exception as e:
        return jsonify({"error":"Error al guardar","detail":str(e)}),500

    return jsonify({"message":"Horario guardado",**res}),201


logging.basicConfig(level=logging.INFO,format="%(asctime)s - %(levelname)s - %(message)s")
if __name__=="__main__":
    print("🚀 API Gandarías v3.1 minimal → http://localhost:5000")
    app.run(host="0.0.0.0",port=5000,debug=True)
