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
    "host":     "gandarias-db.postgres.database.azure.com",
    "port":     5432,
    "dbname":   "postgres",
    "user":     "Admingandarias",
    "password": "Gandarias1.",
    "sslmode":  "require",
}

# ───────── PARÁMETROS ─────────
MIN_HOURS_BETWEEN_SHIFTS = 9
MIN_HOURS_BETWEEN_SPLIT = 4
MAX_SHIFTS_CONTINUOUS = 1
MAX_SHIFTS_SPLIT = 2
MAX_SHIFTS_HYBRID = 4
MAX_DAYS_PER_WEEK = 6


def uid(): return str(uuid.uuid4())
def now(): return datetime.now(timezone.utc)

# ───────── EXCEPCIONES ─────────


class DatabaseConnectionError(Exception):
    ...


class DataNotFoundError(Exception):
    ...


class DataIntegrityError(Exception):
    ...


class ScheduleGenerationError(Exception):
    ...

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

# ───────── HELPERS BD ─────────

# ───────── AGRUPACIÓN DE DEMANDAS ─────────
def _t2m(t: time) -> int:
    return t.hour * 60 + t.minute

def _m2t(m: int) -> time:
    return time(m // 60, m % 60)
MAX_SHIFT_DURATION_HOURS = 8
def coalesce_demands(demands, tolerate_gap_min: int = 0):
    """
    Une demandas contiguas del mismo día/puesto cuando
    no hay hueco (o el hueco <= tolerate_gap_min) y el 'need' es igual.
    Devuelve una nueva lista de Demand con tramos largos.
    """
    # Agrupar por (fecha, workstation)
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
            # Calcular duración si se une este turno
            potential_duration_min = _t2m(nxt.end) - _t2m(curr.start)
            potential_duration_hours = potential_duration_min / 60.0
            
            # ¿Mismo need, contiguas Y no excede duración máxima?
            if (nxt.need == curr.need
                and _t2m(nxt.start) - _t2m(curr.end) <= tolerate_gap_min
                and potential_duration_hours <= MAX_SHIFT_DURATION_HOURS):  # ← NUEVA RESTRICCIÓN
                # Extender el tramo actual
                curr.end = nxt.end
            else:
                merged.append(curr)
                curr = nxt
        merged.append(curr)

    # Mantener el mismo tipo (Demand)
    out = []
    for d in merged:
        out.append(Demand((
            d.id, d.date, d.wsid, d.wsname, d.start, d.end, d.need
        )))
    return out



def conn():
    try:
        return psycopg2.connect(**DB)
    except OperationalError as e:
        t = str(e)
        if "could not connect" in t:
            raise DatabaseConnectionError(
                "No se puede conectar al servidor de BD")
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
    Selección de plantilla (ignorando el año en Start/End):
      1) Si hay UNA activa → usarla.
      2) Si no, ordenar TODAS por cercanía a la semana pedida:
         - dist_días = 0 si SOLAPA; si no, distancia mínima a la semana.
         - desempate: menor distancia al CENTRO de la semana.
         - luego (solo para LOG) mostramos demandas.
         Finalmente, SELECCIONAR la PRIMERA con demandas > 0.
         Si la #1 tiene 0 demandas, se pasa a la #2, etc.
      3) Si ninguna tiene demandas > 0 → error.
    """
    print(f"\n{'='*60}")
    print(f"[PICK_TEMPLATE] Buscando plantilla para semana {week_start} a {week_end}")
    print(f"[PICK_TEMPLATE] Mes solicitado: {week_start.month} ({week_start.strftime('%B')})")
    print(f"{'='*60}")

    # 1) Plantilla activa única
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

    # 2) Traer todas con sus demandas y fecha de creación (para logs/desempates secundarios)
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

    # Helpers
    def md(d: date) -> tuple[int, int]:
        return d.month, d.day

    def same_year(year: int, m: int, d: int) -> date:
        # Manejar 29/02 en años no bisiestos
        try:
            return date(year, m, d)
        except ValueError:
            return date(year, 2, 28) if (m == 2 and d == 29) else date(year, m, d)

    week_center = week_start + (week_end - week_start) // 2

    def distance_metrics(start_md: tuple[int, int], end_md: tuple[int, int]) -> tuple[int, int]:
        """
        Devuelve (distancia_min_dias, distancia_centro_abs) entre el rango de la
        plantilla y la semana pedida (ambos en el año de la semana).
        dist = 0 si hay solape real; si no, distancia al borde más cercano.
        Para rangos que cruzan año, se parte en 2 segmentos y se toma el mejor.
        """
        y = week_start.year
        s = same_year(y, start_md[0], start_md[1])
        e = same_year(y, end_md[0],   end_md[1])

        segments = []
        if s <= e:
            segments.append((s, e))
        else:
            # Cruce Dic→Ene
            segments.append((s, date(y, 12, 31)))
            segments.append((date(y, 1, 1), e))

        def seg_dist(a: date, b: date):
            # 0 si solapa
            if not (b < week_start or a > week_end):
                return 0, 0
            # distancia al borde + distancia al centro (absoluta)
            if b < week_start:
                d1 = (week_start - b).days
                d2 = abs((week_center - b).days)
            else:  # a > week_end
                d1 = (a - week_end).days
                d2 = abs((a - week_center).days)
            return d1, d2

        return min((seg_dist(a, b) for (a, b) in segments), key=lambda x: (x[0], x[1]))

    # Calcular distancias y ordenar SOLO por cercanía
    scored = []
    for tid, name, sdate, edate, created, demandas in rows:
        dist, dcenter = distance_metrics(md(sdate), md(edate))
        scored.append({
            "id": tid, "name": name, "start": sdate, "end": edate,
            "created": created, "demandas": int(demandas or 0),
            "dist": dist, "dcenter": dcenter
        })

    # Orden principal: MÁS CERRADA → por dist, luego por centro
    scored.sort(key=lambda r: (r["dist"], r["dcenter"]))

    # Log top 5 candidatos por cercanía
    print("\n[PICK_TEMPLATE] Ranking por cercanía (top 5):")
    for i, r in enumerate(scored[:5], 1):
        print(f"  {i:>2}. {r['name']:<24}  dist={r['dist']:>2}  dcenter={r['dcenter']:>2}  demandas={r['demandas']}  ({r['start']}..{r['end']})")

    # Elegir la PRIMERA con demandas > 0 (si la #1 tiene 0, pasar a la #2, etc.)
    chosen = next((r for r in scored if r["demandas"] > 0), None)
    if chosen:
        print(f"\n✓ ENCONTRADA por cercanía con demandas: '{chosen['name']}'")
        print(f"  Rango: {chosen['start']} a {chosen['end']} | demandas={chosen['demandas']} | dist={chosen['dist']} dcenter={chosen['dcenter']}")
        return (chosen["id"], chosen["name"])

    # 3) Ninguna tiene demandas
    print("\n[PICK_TEMPLATE] ✗ Ninguna candidata cercana tiene demandas > 0")
    raise DataNotFoundError("No se encontró ninguna plantilla con demandas > 0")


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
        demands = coalesce_demands(demands, tolerate_gap_min=0)
        if not demands:
            raise DataNotFoundError(
                "La plantilla seleccionada no tiene demandas")

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

        # Restricciones exactas
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

        # Licencias → VAC
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

        # Ausentismos → ABS
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


def solve(emps: List[Emp], dem: List[Demand], week: List[date]):
    """Solver original (estricto) - requiere 100% de cobertura"""
    mdl = cp_model.CpModel()
    X = {}
    for d in dem:
        for e in emps:
            if e.can(d.wsid) and e.available(d.date, d.start, d.end):
                X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    if not X:
        raise ScheduleGenerationError(
            "Sin variables: nadie puede cubrir demandas")

    # cubrir demanda
    for d in dem:
        mdl.Add(sum(X[e.id, d.id]
                for e in emps if (e.id, d.id) in X) == d.need)

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
                            mdl.Add(X[e.id, lst[i].id] +
                                    X[e.id, lst[j].id] <= 1)

    # límites/día
    for e in emps:
        for d in week:
            vs = [X[e.id, dm.id]
                  for dm in dem if dm.date == d and (e.id, dm.id) in X]
            if vs:
                maxs = MAX_SHIFTS_HYBRID if e.is_hybrid(
                ) else MAX_SHIFTS_SPLIT if e.split else MAX_SHIFTS_CONTINUOUS
                mdl.Add(sum(vs) <= maxs)

    # máx días/sem
    for e in emps:
        mdl.Add(sum(X[e.id, d.id]
                for d in dem if (e.id, d.id) in X) <= MAX_DAYS_PER_WEEK)

    # descanso ≥9h
    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id, a.id) in X and (e.id, b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS*60:
                        mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    # bloques partidos ≥4h
    for e in emps:
        if not e.split:
            continue
        for d in by_day:
            lst = [dm for dm in dem if dm.date == d]
            for i in range(len(lst)):
                for j in range(i+1, len(lst)):
                    a, b = lst[i], lst[j]
                    if (e.id, a.id) in X and (e.id, b.id) in X and not overlap(a, b):
                        if 0 < (to_min(b.start)-to_min(a.end))/60 < MIN_HOURS_BETWEEN_SPLIT:
                            mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

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
    Prioriza maximizar la cobertura real vs. fallar completamente.
    """
    mdl = cp_model.CpModel()
    X = {}
    
    # Variables de asignación (mismo que antes)
    for d in dem:
        for e in emps:
            if e.can(d.wsid) and e.available(d.date, d.start, d.end):
                X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")
    
    if not X:
        raise ScheduleGenerationError("Sin variables: nadie puede cubrir demandas")

    # 🔥 CAMBIO CLAVE: Variables de demanda NO cubierta
    unmet_demand = {}
    for d in dem:
        unmet_demand[d.id] = mdl.NewIntVar(0, d.need, f"unmet_{d.id}")
    
    # 🔥 NUEVA RESTRICCIÓN: Cubrir lo que se pueda (no obligatorio al 100%)
    for d in dem:
        covered = sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X)
        mdl.Add(covered + unmet_demand[d.id] == d.need)
    
    # Restricciones de empleados (mismas que antes)
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

    # Límites por día
    for e in emps:
        for d in week:
            vs = [X[e.id, dm.id] for dm in dem if dm.date == d and (e.id, dm.id) in X]
            if vs:
                maxs = MAX_SHIFTS_HYBRID if e.is_hybrid() else MAX_SHIFTS_SPLIT if e.split else MAX_SHIFTS_CONTINUOUS
                mdl.Add(sum(vs) <= maxs)

    # Máximo días por semana
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
        for d in by_day:
            lst = [dm for dm in dem if dm.date == d]
            for i in range(len(lst)):
                for j in range(i+1, len(lst)):
                    a, b = lst[i], lst[j]
                    if (e.id, a.id) in X and (e.id, b.id) in X and not overlap(a, b):
                        if 0 < (to_min(b.start)-to_min(a.end))/60 < MIN_HOURS_BETWEEN_SPLIT:
                            mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    # 🎯 OBJETIVO: Minimizar demanda no cubierta (maximizar cobertura)
    total_unmet = sum(unmet_demand[d.id] for d in dem)
    mdl.Minimize(total_unmet)

    # Resolver
    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = 120
    status = sol.Solve(mdl)
    
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ScheduleGenerationError("Modelo sin solución factible")

    # Procesar resultados y mostrar estadísticas
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
        
        # Agregar asignaciones reales
        for e in emps:
            if (e.id, d.id) in X and sol.Value(X[e.id, d.id]):
                out[d.date].append((e, d))
    
    # Log de cobertura
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
    
    # Mostrar problemas críticos (cobertura < 50%)
    critical_issues = [stats for stats in coverage_stats.values() if stats['coverage_pct'] < 50]
    if critical_issues:
        print(f"\n⚠️  TURNOS CON COBERTURA CRÍTICA (<50%):")
        for stats in critical_issues:
            d = stats['demand']
            print(f"   📅 {d.date} {d.start}-{d.end} {d.wsname}: {stats['covered']}/{d.need} ({stats['coverage_pct']}%)")
    
    # Mostrar cobertura por puesto
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
    Calcula la observación (BT/C) para un empleado en un turno específico.
    
    BT (Bajo Turno): El empleado puede trabajar más turnos ese día
    C (Cierre): El empleado ha alcanzado su máximo de turnos del día
    "" (vacío): Turnos fijos o normales sin marcación especial
    """
    # Si esta fila es de turno fijo → nunca BT/C
    if (emp.id, dm.id) in fixed_ids:
        return ""
    
    # Contar cuántos turnos tiene asignados el empleado en este día
    cnt = sum(1 for e, _ in assigns_day if e.id == emp.id)
    
    # Determinar el máximo de turnos según el tipo de empleado
    if emp.is_hybrid():  # 4 o más roles
        maxs = MAX_SHIFTS_HYBRID
    elif emp.split:  # Acepta turnos partidos
        maxs = MAX_SHIFTS_SPLIT
    else:  # Empleado normal
        maxs = MAX_SHIFTS_CONTINUOUS
    
    # Aplicar lógica BT/C
    if cnt < maxs:
        return "BT"  # Puede trabajar más turnos
    elif cnt >= maxs:
        return "C"   # Ha alcanzado el máximo
    else:
        return ""    # No debería llegar aquí

# ───────── FUNCIONES GENERATE ─────────


def generate(week_start: date):
    """Generación original (estricta) - requiere 100% de cobertura"""
    emps, demands, tpl, week, fixed = load_data(week_start)
    sched = solve(emps, demands, week)
    
    # añadir turnos fijos
    for d, lst in fixed.items():
        sched[d].extend(lst)

    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    # Añadir ausencias/licencias al preview
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
    """
    Versión flexible de generate() que acepta cobertura parcial
    """
    emps, demands, tpl, week, fixed = load_data(week_start)
    
    # Usar el solver flexible
    sched, coverage_stats = solve_flexible(emps, demands, week)
    
    # Añadir turnos fijos
    for d, lst in fixed.items():
        sched[d].extend(lst)

    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    # Añadir ausencias/licencias al preview
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

    # Calcular estadísticas actualizadas
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
            "flexible_mode": True  # Indicador de que se usó modo flexible
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
            st["checks"]["database"] = {"status": "healthy", "version": cur.fetchone()[
                0].split(',')[0]}
            st["status"] = "healthy"
    except Exception as e:
        st["checks"]["database"] = {"status": "unhealthy", "message": str(e)}
        st["status"] = "unhealthy"
    return jsonify(st), 200 if st["status"] == "healthy" else 503


@app.route('/api/agenda/preview')
def preview():
    wk = request.args.get('week_start')
    flexible = request.args.get('flexible', 'true').lower() == 'true'  # Por defecto flexible
    
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
            res, _, _, _, _ = generate(ws)  # Versión original (estricta)
        return jsonify(res), 200
    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
        return jsonify({"error": str(e)}), 400


@app.route('/api/agenda/save', methods=['POST'])
def save():
    data = request.get_json() or {}
    wk = data.get('week_start')
    force = data.get('force', False)
    flexible = data.get('flexible', True)  # Por defecto flexible
    
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
            # ¿Existe horario previo para la semana?
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

            # Insertar cada asignación
            for d, ass in sched.items():
                for emp, dm in ass:
                    if dm.wsid is None:
                        # AUSENCIAS
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
                        # Turno normal
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
    """
    Endpoint para diagnosticar problemas de cobertura antes de generar horarios
    """
    wk = request.args.get('week_start')
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    try:
        emps, demands, tpl, week, fixed = load_data(ws)
        
        # Análizar capacidad vs demanda por puesto
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
                # Buscar nombre del workstation
                ws_name = next((d.wsname for d in demands if d.wsid == ws_id), None)
                if ws_name:
                    workstation_analysis[ws_name]['available_employees'] += 1
                    workstation_analysis[ws_name]['employee_names'].append(emp.name)
        
        # Calcular cobertura teórica máxima
        for ws_name, data in workstation_analysis.items():
            # Asumiendo que cada empleado puede trabajar máximo 6 días x 2 turnos = 12 turnos/semana
            max_coverage = data['available_employees'] * 12
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
    """
    Endpoint para comparar resultados entre modo estricto y flexible
    """
    wk = request.args.get('week_start')
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400
    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    try:
        # Intentar modo estricto
        strict_result = None
        strict_error = None
        try:
            strict_result, _, _, _, _ = generate(ws)
        except Exception as e:
            strict_error = str(e)
        
        # Intentar modo flexible
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
    print("   • Endpoint /api/agenda/diagnostics")
    print("   • Endpoint /api/agenda/comparison") 
    print("   • Parámetros flexible=true/false en preview y save")
    app.run(host="0.0.0.0", port=5000, debug=True)