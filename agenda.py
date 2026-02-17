#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AGENDA GENERATOR API – Gandarías v3.15c (determinista + reglas split + fallback greedy)
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
from typing import Iterable, Dict, Tuple, List, Set, Any
from services.explicador_huecos import ExplicadorHuecosService, ContextoExplicacion
from collections import defaultdict

import psycopg2
from flask import Flask, jsonify, request
from flask_cors import CORS
from ortools.sat.python import cp_model
from psycopg2 import DataError, OperationalError, ProgrammingError


# ───────── CONFIG GENERAL ─────────
ASCII_LOGS = True
ENFORCE_PEAK_CAP = False
PEAK_CAP_LOG = True
MIN_HOURS_BETWEEN_SHIFTS = 9
MIN_HOURS_BETWEEN_SPLIT = 3 
MIN_SEGMENT_MINUTES = 15    # ← se sobreescribe desde BD (regla adicional)
# Semana “contable” de negocio: Lun(0)–Sab(5)
BUSINESS_DAYS = {0, 1, 2, 3, 4, 5}   # Lunes–Sábado
MAX_BUSINESS_DAYS_OFF = 2            # ⇒ como mucho 2 días sin trabajar en esos 6
MAX_HOURS_PER_DAY = 9
MIN_SHIFT_DURATION_HOURS = 3
HARD_REQUIRE_USERSHIFT = True

# Pesos
WEIGHT_MUST_HAVE_ONE = 200_000
WEIGHT_ULTRA_SLOT0   = 500_000
WEIGHT_SHORT_SLOT    = 100_000
WEIGHT_CONSOLIDATE   = 250
WEIGHT_USERWINDOW    = 80_000
WEIGHT_FAIR_FREE = 5 
WEIGHT_RESTRICTED_PRIORITY_SHORTFALL = 60000 
# Prefiere arrancar el UserShift en el primer segmento disponible del día (suave)
WEIGHT_US_ANCHOR_START = 80_000


WEIGHT_DAYS_OFF = 80_000 # penalización por incumplir "máx 2 días sin trabajar"
CRITICAL_WS_NAMES = {"APERTURA", "APOYO ENLACE", "Apertura", "ENLACE", "JEFE BARRA", "Jefe Barra"}


ROLE_FALLBACKS_BY_NAME = {
    "JEFE BARRA": ["ENLACE", "APOYO ENLACE", "CAMARERO BARRA"],
    "ENLACE": ["APOYO ENLACE"],
    "JEFE COMEDOR": ["CAMARERO COMEDOR"],
    "CAMARERO BARRA": ["APERTURA BARRA"],
}
WEIGHT_ROLE_DOWNGRADE = 500
NIGHT_BOOST_FROM = 21 * 60  # 21:00
WEIGHT_CRITICAL_NIGHT_MULT = 5
WEIGHT_CRITICAL_UNMET = 10
WEIGHT_BALANCE_OVERRIDE = 50   # peso suave para repartir carga en días libre
MAX_DAYS_PER_WEEK = 6          # tope duro: 6 días trabajados / semana
# Penalización por desigualdad de DÍAS trabajados (sólo en modo libre)
WEIGHT_FAIR_FREE_DAYS = 30000
# Penalización L1 por desigualdad de DÍAS en libre (más fuerte que spread)
WEIGHT_FAIR_FREE_DAYS_L1 = 120_000




# ───────── FLASK ─────────
app = Flask(__name__)
CORS(app)

# ───────── BD ─────────
DB = {
  "host": "database-gandarias.ct6gmyi80fdr.eu-central-1.rds.amazonaws.com",
  "port": 5432,
  "dbname": "postgres",
  "user": "postgres",
  "password": "MyStrongPassword!123_",
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
        self.shift_type_restr_by_dow = defaultdict(set)  # dow -> {shiftTypeId}
        self.shift_type_windows = defaultdict(list)      # dow -> [(start,end)] derivadas del ST
        self.us_two_starts_dow: Set[int] = set()
        self.user_shift_anchor_by_date = {}   # date -> time (primer inicio viable dentro de la ventana)



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
        """
        row = (Id, Date, WorkstationId, WorkstationName, Start, End, EffortRequired)
        EffortRequired puede ser 0.5 en los puestos híbridos.
        """
        (self.id, rdate, self.wsid, self.wsname, self.start, self.end, need) = row

        # Fecha normalizada
        self.date = rdate.date() if hasattr(rdate, 'date') else rdate

        # Guardamos el valor "crudo" que viene de BD (incluye 0.5)
        try:
            self.raw_need = float(need) if need is not None else 0.0
        except (TypeError, ValueError):
            self.raw_need = 0.0

        # Marcar si es híbrido (EffortRequired = 0.5)
        self.is_hybrid_05 = abs(self.raw_need - 0.5) < 1e-6

        # El solver trabaja con enteros:
        # - los 0.5 los tratamos como 1 "slot" cada uno
        # - los demás se redondean al entero más cercano positivo
        if self.is_hybrid_05:
            self.need = 1
        else:
            self.need = int(round(self.raw_need)) if self.raw_need > 0 else 0

        # Índice de slot (lo usas más adelante en el solver)
        self.slot_index = 0
        self.shift_type = None

    def __repr__(self):
        return (f"Demand(id={self.id}, date={self.date}, ws={self.wsname}, "
                f"{self.start}-{self.end}, raw_need={getattr(self, 'raw_need', '?')}, "
                f"need={self.need}, hybrid={getattr(self, 'is_hybrid_05', False)})")

# ───────── HELPERS ─────────
def _end_for_calc(t: time) -> time:
    # tratamos 00:00 como 23:59 (fin de día)
    return t if t != time(0,0) else time(23,59)

def _intersect_minutes(a_s: time, a_e: time, b_s: time, b_e: time) -> int:
    a1 = _t2m(a_s); a2 = _t2m(_end_for_calc(a_e))
    b1 = _t2m(b_s); b2 = _t2m(_end_for_calc(b_e))
    lo = max(a1, b1); hi = min(a2, b2)
    return max(0, hi - lo)

def _has_at_least_3h_inside_st_within_us(e: 'Emp', dow: int) -> bool:
    """
    ¿Existe alguna intersección US∩ST con >= 3h seguidas?
    Si sí, entonces NO es 'caso Félix'. Si no, SÍ es 'caso Félix'.
    """
    us_wins = e.user_shift_windows.get(dow, [])
    st_wins = e.shift_type_windows.get(dow, [])
    if not us_wins:
        return True  # no es día con US → no lo tratamos como conflicto ST
    if not st_wins:
        return False  # sin ST → consideramos conflicto (caso Félix)

    min_need = MIN_SHIFT_DURATION_HOURS * 60
    best = 0
    for (us_s, us_e) in us_wins:
        for (st_s, st_e) in st_wins:
            best = max(best, _intersect_minutes(us_s, us_e, st_s, st_e))
            if best >= min_need:
                return True
    return False

def _is_felix_like_day(e: 'Emp', day: date, overrides: set[tuple[str, date]]) -> bool:
    """
    'Caso Félix' = (i) ese día tiene ≥2 ventanas de US y (ii) ST no cubre ni 3h seguidas dentro de US.
    Además, solo aplica cuando NO es override (porque en override ya vamos en libre).
    """
    if (e.id, day) in overrides:
        return False
    dow = day.weekday()
    if len(e.user_shift_windows.get(dow, [])) < 2:
        return False
    return not _has_at_least_3h_inside_st_within_us(e, dow)



def add_max_days_worked_per_week(mdl, emps, dem, X, week, max_days=6):
    """
    Tope duro: cada empleado puede 'activar' como mucho max_days días en la semana.
    Cuenta cualquier día con alguna asignación (cualquier puesto).
    """
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    for e in emps:
        day_flags = []
        for day in week:
            todays = [dm for dm in by_day.get(day, []) if (e.id, dm.id) in X]
            if not todays:
                continue
            y = mdl.NewBoolVar(f"y_work_any_{e.id}_{day.isoformat()}")
            mdl.Add(sum(X[e.id, dm.id] for dm in todays) >= y)
            mdl.Add(sum(X[e.id, dm.id] for dm in todays) <= 1000 * y)
            day_flags.append(y)
        if day_flags:
            mdl.Add(sum(day_flags) <= max_days)

def add_balance_override_workload_soft(mdl, emps, dem, X, week, overrides, weight=50):
    """
    Suaviza desigualdades SOLO en días en 'override' (asignación libre).
    Minimiza (máx - mín) de minutos trabajados en override entre empleados.
    Devuelve una expresión linear (weight * spread) para restarla al objetivo de maximización.
    """
    if not weight or weight <= 0:
        return 0

    total_cap = MAX_HOURS_PER_DAY * 60 * len(week)  # cota segura
    T_over = {}  # minutos por empleado en días override

    for e in emps:
        terms = []
        for dm in dem:
            if (e.id, dm.id) in X and (e.id, dm.date) in overrides:
                terms.append(duration_min(dm) * X[e.id, dm.id])
        if terms:
            t = mdl.NewIntVar(0, total_cap, f"T_over_{e.id}")
            mdl.Add(t == sum(terms))
            T_over[e.id] = t

    if len(T_over) <= 1:
        return 0

    z_max = mdl.NewIntVar(0, total_cap, "Z_over_max")
    z_min = mdl.NewIntVar(0, total_cap, "Z_over_min")
    for t in T_over.values():
        mdl.Add(t <= z_max)
        mdl.Add(t >= z_min)

    spread = mdl.NewIntVar(0, total_cap, "Z_over_spread")
    mdl.Add(spread == z_max - z_min)
    return weight * spread


def squash_micro_segments(demands, min_min=MIN_SEGMENT_MINUTES):
    """
    Fusiona con el vecino contiguo los segmentos < min_min.
    Si no hay vecino contiguo, los descarta (log).
    """
   
    by_key = defaultdict(list)
    for d in demands:
        by_key[(d.date, d.wsid, d.wsname)].append(d)

    out = []
    for (dt, wsid, wsname), items in by_key.items():
        items.sort(key=lambda x: (_t2m(x.start),
                                  _t2m(x.end if x.end != time(0,0) else time(23,59))))
        i = 0
        while i < len(items):
            cur = items[i]
            dur = duration_min(cur)
            if dur >= min_min or len(items) == 1:
                out.append(cur); i += 1; continue

            # intentar fusionar con el anterior contiguo
            if out and out[-1].date == cur.date and out[-1].wsid == cur.wsid:
                prev = out[-1]
                prev_end = _t2m(prev.end if prev.end != time(0,0) else time(23,59))
                if prev_end == _t2m(cur.start):
                    prev.end = cur.end
                    i += 1
                    continue
            # intentar fusionar con el siguiente contiguo
            if i+1 < len(items):
                nxt = items[i+1]
                cur_end = _t2m(cur.end if cur.end != time(0,0) else time(23,59))
                if cur_end == _t2m(nxt.start):
                    nxt.start = cur.start
                    i += 1
                    continue

            if ASCII_LOGS:
                print(f"[MICRO-SEGMENT] descartado {wsname} {dt} {cur.start}-{cur.end} (<{min_min}m)")
            i += 1
    return out

def add_min_per_contiguous_block_global_enforced(mdl, emps, dem, X,
                                                 overrides: set[tuple[str, date]],
                                                 min_hours: int):
    """Si un empleado activa cualquier segmento en un día (NO override),
    cada BLOQUE CONTIGUO global (encadenando turnos de cualquier puesto con
    start_{k+1} == end_k) debe sumar al menos min_hours.
    """
    if not min_hours or min_hours <= 0:
        return
    min_min = int(min_hours * 60)

    # Agrupar solo por día (global, no por workstation)
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    def tend(t: time) -> time:
        return t if t != time(0,0) else time(23,59)

    for e in emps:
        for day, lst in by_day.items():
            if (e.id, day) in overrides:
                continue  # en override este mínimo se gestiona con la variante "free"
            lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(tend(z.end))))
            n = len(lst)
            i = 0
            while i < n:
                j = i
                cur_end = _t2m(tend(lst[i].end))
                minutes_terms, used_vars = [], []
                if (e.id, lst[i].id) in X:
                    minutes_terms.append(duration_min(lst[i]) * X[e.id, lst[i].id])
                    used_vars.append(X[e.id, lst[i].id])

                # encadenar contiguos EXACTOS, mezclando puestos
                while j + 1 < n and _t2m(lst[j+1].start) == cur_end:
                    j += 1
                    cur_end = _t2m(tend(lst[j].end))
                    if (e.id, lst[j].id) in X:
                        minutes_terms.append(duration_min(lst[j]) * X[e.id, lst[j].id])
                        used_vars.append(X[e.id, lst[j].id])

                if used_vars:
                    y_blk = mdl.NewBoolVar(f"blk_global_enf_{e.id}_{day.isoformat()}_{i}_{j}")
                    mdl.Add(sum(used_vars) >= y_blk)
                    mdl.Add(sum(used_vars) <= 1000 * y_blk)
                    mdl.Add(sum(minutes_terms) >= min_min * y_blk)
                i = j + 1
def build_free_mode_balance_days_L1_penalty(mdl, emps, dem, X, overrides_emp_day):
    """
    Penaliza la DESIGUALDAD de DÍAS trabajados por persona SOLO en días override,
    usando L1: sum_e |D_e - M|, donde D_e es # de días libres trabajados y M es un centro elegido por el modelo.
    Es más potente que usar sólo 'spread = max - min'.
    """
   
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    # D_e: número de días (en override) donde el empleado e trabajó al menos un segmento
    De = {}
    for e in emps:
        terms = []
        for day, lst in by_day.items():
            if (e.id, day) not in overrides_emp_day:
                continue
            todays = [(e.id, dm.id) for dm in lst if (e.id, dm.id) in X]
            if not todays:
                continue
            y = mdl.NewBoolVar(f"y_free_work_{e.id}_{day.isoformat()}")
            mdl.Add(sum(X[k] for k in todays) >= y)
            mdl.Add(sum(X[k] for k in todays) <= 1000 * y)
            terms.append(y)
        if terms:
            di = mdl.NewIntVar(0, 7, f"Dfree_{e.id}")
            mdl.Add(di == sum(terms))
            De[e.id] = di

    if not De:
        return 0

    # Centro M (0..7)
    M = mdl.NewIntVar(0, 7, "Dfree_center")
    # Desviaciones absolutas
    devs = []
    for eid, di in De.items():
        te = mdl.NewIntVar(0, 7, f"Dfree_dev_{eid}")
        mdl.Add(te >= di - M)
        mdl.Add(te >= M - di)
        devs.append(te)
    return sum(devs)


def build_shifttype_window_penalty(mdl, emps, dem, X, overrides=set()):
    penalties = []
    for d in dem:
        dow = d.date.weekday()
        for e in emps:
            key = (e.id, d.id)
            if key not in X:
                continue

            # Día con US enforzado → ST no penaliza (ya estaba)
            us_enforced = (e.user_shift_windows.get(dow) and (e.id, d.date) not in overrides)
            # ── NUEVO: si es 'caso Félix' este día, ignoramos ST
            if _is_felix_like_day(e, d.date, overrides):
                if ASCII_LOGS:
                    print(f"[ST-BYPASS][{d.date}] {e.name}: dos US-starts y ST no cubre 3h → no penalizamos ST.")
                continue

            if us_enforced:
                continue

            st_wins = e.shift_type_windows.get(dow, [])
            if not st_wins:
                continue

            end = d.end if d.end != time(0,0) else time(23,59)
            in_any = any(d.start >= ws and end <= we for (ws, we) in st_wins)
            if not in_any:
                z = mdl.NewBoolVar(f"pen_outside_st_{e.id}_{d.id}")
                mdl.Add(z >= X[key])
                penalties.append(z)
    return (WEIGHT_USERWINDOW * sum(penalties)) if penalties else 0

def recheck_fill_unmet(emps: list['Emp'],
                       demands: list['Demand'],
                       week: list[date],
                       sched: dict[date, list[tuple['Emp','Demand']]],
                       coverage_stats: dict,
                       overrides: set[tuple[str, date]]) -> None:
    """
    Post-proceso para rellenar demanda no cubierta.
    * Forma BLOQUES CONTIGUOS del mismo WS por día (pero ya NO exige que el bloque alcance 3h por sí solo).
    * Regla de mínimos corregida:
        - Si el empleado ya reúne >= MIN_SHIFT_DURATION_HOURS en el día, se permite añadir bloques más cortos
          siempre que respete GAP entre splits y no solape ni supere topes.
        - Si el empleado aún no llega al mínimo diario, el bloque añadido debe llevar el total del día
          a >= MIN_SHIFT_DURATION_HOURS (no es necesario que un único bloque tenga esa duración).
    * Se respetan: US/ST (en forzado dentro de US), solapes, GAP de splits, MAX_HOURS_PER_DAY y MAX_DAYS_PER_WEEK.
    * Prioriza a quienes tienen menos minutos HOY (y luego menos en la semana).
    Modifica in-place: sched y coverage_stats.
    """
    from collections import defaultdict

    def _end_for_calc(t: time) -> time:
        return t if t != time(0, 0) else time(23, 59)

    def _dm_iv(dm: 'Demand') -> tuple[int,int]:
        return _t2m(dm.start), _t2m(_end_for_calc(dm.end))

    def _contiguous(dma: 'Demand', dmb: 'Demand') -> bool:
        if dma.date != dmb.date or (dma.wsid is None) or (dmb.wsid is None):
            return False
        if (dma.wsname or "").strip().upper() != (dmb.wsname or "").strip().upper():
            return False
        sa, ea = _dm_iv(dma); sb, eb = _dm_iv(dmb)
        return ea == sb

    def _can_cover_ws(e: 'Emp', wsname: str) -> bool:
        if e.can(wsname):
            return True
        for fb in ROLE_FALLBACKS_BY_NAME.get(wsname, []):
            if e.can(fb):
                return True
        return False

    def _allowed_by_usershift(e: 'Emp', dm: 'Demand') -> bool:
        # Si el día está en override: se permite fuera de US, pero igual aplica el mínimo diario.
        if (e.id, dm.date) in overrides:
            return True
        return inside_usershift_window(e, dm, overrides)

    def _build_usage():
        used_any = defaultdict(lambda: defaultdict(list))   # eid -> day -> [(s,e)]
        minutes_by_day = defaultdict(lambda: defaultdict(int))
        minutes_by_week = defaultdict(int)
        days_worked = defaultdict(set)
        for dday, pairs in sched.items():
            for e, dm in pairs:
                s, e_end = _dm_iv(dm)
                used_any[e.id][dday].append((s, e_end))
                minutes_by_day[e.id][dday] += (e_end - s)
                minutes_by_week[e.id] += (e_end - s)
                if dm.wsid is not None:
                    days_worked[e.id].add(dday)
        for eid in list(used_any.keys()):
            for dday in list(used_any[eid].keys()):
                used_any[eid][dday] = _merge_sorted(used_any[eid][dday])
        return used_any, minutes_by_day, minutes_by_week, days_worked

    def _fits_daily_caps(e: 'Emp', day: date, extra_min: int, minutes_today: int, days_worked_count: int) -> bool:
        if minutes_today + extra_min > MAX_HOURS_PER_DAY * 60:
            return False
        inc_day = 0 if minutes_today > 0 else 1
        return (days_worked_count + inc_day) <= MAX_DAYS_PER_WEEK

    def _validate_after_merge(e: 'Emp',
                              day: date,
                              used_today: list[tuple[int,int]],
                              add_block: list[tuple[int,int]]) -> bool:
        """
        Valida:
        - Gaps entre bloques >= MIN_HOURS_BETWEEN_SPLIT
        - Si minutos_previos < mínimo, entonces minutos_totales_post >= mínimo
        - Si minutos_previos >= mínimo, se aceptan agregados más cortos
        """
        merged = _merge_sorted(used_today + add_block)
        if not _respect_split_gap(merged, MIN_HOURS_BETWEEN_SPLIT):
            return False

        minutes_previos = sum(b - a for a, b in used_today)
        total_dia = sum(b - a for a, b in merged)
        min_req = MIN_SHIFT_DURATION_HOURS * 60

        if minutes_previos >= min_req:
            return True  # ya cumplía el mínimo, el agregado es válido por GAP
        else:
            return total_dia >= min_req

    def _choose_candidates(day: date, wsname: str):
        cands = []
        for e in emps:
            if not _can_cover_ws(e, wsname):
                continue
            cands.append((minutes_by_day[e.id].get(day, 0), minutes_by_week[e.id], e))
        cands.sort(key=lambda t: (t[0], t[1]))
        return cands

    # --- Estado inicial
    used_any, minutes_by_day, minutes_by_week, days_worked = _build_usage()

    # unmet por dm
    unmet_left = {dm.id: max(0, (coverage_stats.get(dm.id) or {}).get("unmet", getattr(dm, "need", 0))) for dm in demands}

    # DMs con unmet por día y WS
    from collections import defaultdict as _dd
    dms_by_day_ws = _dd(lambda: _dd(list))
    for dm in demands:
        st = coverage_stats.get(dm.id)
        if not st or dm.wsid is None:
            continue
        if st["unmet"] > 0:
            dms_by_day_ws[dm.date][dm.wsname].append(dm)

    for day in list(dms_by_day_ws.keys()):
        for ws in list(dms_by_day_ws[day].keys()):
            dms_by_day_ws[day][ws].sort(key=lambda d: (_t2m(d.start), _t2m(_end_for_calc(d.end))))

    touched_days: set[date] = set()

    # --- Relleno por runs contiguos
    for day, wsmap in dms_by_day_ws.items():
        for wsname, dm_list in wsmap.items():
            idx = 0
            while idx < len(dm_list):
                dm0 = dm_list[idx]
                if unmet_left.get(dm0.id, 0) <= 0:
                    idx += 1
                    continue

                # Construir RUN contiguo
                run = [dm0]
                j = idx + 1
                while j < len(dm_list) and _contiguous(dm_list[j - 1], dm_list[j]):
                    run.append(dm_list[j])
                    j += 1

                # Probar candidatos (menos carga hoy/semana primero)
                assigned = False
                candidates = _choose_candidates(day, wsname)

                for _, _, e in candidates:
                    todays = used_any[e.id].get(day, [])
                    minutes_today = minutes_by_day[e.id].get(day, 0)
                    need_min_today = max(0, MIN_SHIFT_DURATION_HOURS * 60 - minutes_today)

                    # construir bloque con la menor cantidad de slots del RUN que:
                    #   - el empleado pueda cubrir,
                    #   - no solape,
                    #   - y nos acerque a need_min_today (si es > 0); si need_min_today == 0, tomar el primer slot válido.
                    block_ivs: list[tuple[int,int]] = []
                    block_dms: list['Demand'] = []
                    tmp_used = todays[:]
                    acc = 0

                    for dm in run:
                        if unmet_left.get(dm.id, 0) <= 0:
                            continue
                        if not _allowed_by_usershift(e, dm):
                            continue
                        s, e_end = _dm_iv(dm)
                        if not e.available(day, _m2t(s), _m2t(e_end)):
                            continue
                        if _has_overlap(tmp_used, s, e_end):
                            continue

                        # Tentativamente añadir
                        block_ivs.append((s, e_end))
                        block_dms.append(dm)
                        tmp_used = _merge_sorted(tmp_used + [(s, e_end)])
                        acc += (e_end - s)

                        # Si ya cumplimos con need_min_today, podemos parar (greedy)
                        if need_min_today > 0 and acc >= need_min_today:
                            break
                        # Si ya teníamos el mínimo, basta con el primer slot válido
                        if need_min_today == 0 and acc > 0:
                            break

                    if not block_ivs:
                        continue

                    extra_min = sum(b - a for a, b in block_ivs)
                    # Topes diarios
                    if not _fits_daily_caps(e, day, extra_min, minutes_today, len(days_worked[e.id])):
                        continue

                    if not _validate_after_merge(e, day, todays, block_ivs):
                        continue

                    # Confirmar: insertar todos los dms del bloque
                    for dm in block_dms:
                        if unmet_left.get(dm.id, 0) <= 0:
                            continue
                        s, e_end = _dm_iv(dm)
                        sched.setdefault(day, []).append((e, dm))
                        unmet_left[dm.id] -= 1
                        st = coverage_stats[dm.id]
                        st["covered"] += 1
                        st["unmet"] = max(0, st["unmet"] - 1)
                        if "employees" not in st:
                            st["employees"] = []
                        st["employees"].append(e)
                        used_any[e.id][day] = _merge_sorted(used_any[e.id].get(day, []) + [(s, e_end)])
                        minutes_by_day[e.id][day] = minutes_by_day[e.id].get(day, 0) + (e_end - s)
                        minutes_by_week[e.id] += (e_end - s)
                        days_worked[e.id].add(day)
                        touched_days.add(day)

                    assigned = True
                    # tras asignar, no avanzamos idx si aún queda unmet en dm_list[idx]; re-evaluamos
                    break

                if not assigned:
                    # no pudimos cubrir el inicio del RUN -> saltar al final del RUN
                    idx = j
                else:
                    # si ya está cubierto el dm en idx, avanzar al siguiente con unmet>0
                    while idx < len(dm_list) and unmet_left.get(dm_list[idx].id, 0) <= 0:
                        idx += 1

    if touched_days:
        for dday in touched_days:
            sched[dday] = _filter_blocks_min4_and_gap_global(
                sched.get(dday, []),
                overrides,
                MIN_SHIFT_DURATION_HOURS,
                MIN_HOURS_BETWEEN_SPLIT
            )
        # Recalcular coverage
        for dm in demands:
            if dm.wsid is None:
                continue
            covered = sum(1 for e2, d2 in sched.get(dm.date, []) if d2.id == dm.id)
            emps_assigned = [e2 for e2, d2 in sched.get(dm.date, []) if d2.id == dm.id]
            entry = coverage_stats.get(dm.id) or {"demand": dm}
            entry["demand"] = dm
            entry["covered"] = covered
            entry["unmet"] = max(0, dm.need - covered)
            entry["coverage_pct"] = round(covered / dm.need * 100, 1) if dm.need else 100
            entry["employees"] = emps_assigned
            coverage_stats[dm.id] = entry


def apply_hybrid_05_postprocess(
    emps: list["Emp"],
    demands: list["Demand"],
    week: list[date],
    sched: dict[date, list[tuple["Emp", "Demand"]]],
    coverage_stats: dict,
    overrides: dict,
):
    """
    Post-proceso para puestos híbridos (EffortRequired = 0.5).
    
    NUEVA LÓGICA:
    - Agrupa demandas híbridas en BLOQUES CONTINUOS de mínimo 3h y máximo 10h
    - Prueba TODAS las combinaciones de pares hasta encontrar empleados disponibles
    """

    logger = logging.getLogger(__name__)

    if not demands:
        return

    def _tend(t: time) -> time:
        return t if t != time(0, 0) else time(23, 59)

    def _t2m(t: time) -> int:
        return t.hour * 60 + t.minute

    # PASO 1: Limpiar asignaciones híbridas previas
    hybrid_demand_ids = set()
    for dm in demands:
        if getattr(dm, "is_hybrid_05", False):
            hybrid_demand_ids.add(dm.id)

    if hybrid_demand_ids:
        print(f"[HYB05_POST] Limpiando {len(hybrid_demand_ids)} demandas hibridas pre-asignadas...")
        for day in list(sched.keys()):
            sched[day] = [
                (emp, dm)
                for (emp, dm) in sched[day]
                if dm.id not in hybrid_demand_ids
            ]
            if not sched[day]:
                del sched[day]
        for dm_id in hybrid_demand_ids:
            if dm_id in coverage_stats:
                coverage_stats[dm_id]["met"] = 0
                coverage_stats[dm_id]["unmet"] = coverage_stats[dm_id]["demand"].need

    # PASO 2: Agrupar demandas híbridas por (día, puesto)
    # Estructura: {(día, puesto): [lista de demandas ordenadas por hora]}
    from collections import defaultdict
    demands_by_day_ws: dict[tuple[date, str], list] = defaultdict(list)

    for dm in demands:
        if not getattr(dm, "is_hybrid_05", False):
            continue
        key = (dm.date, dm.wsname)
        demands_by_day_ws[key].append(dm)

    # Ordenar por hora de inicio
    for key in demands_by_day_ws:
        demands_by_day_ws[key].sort(key=lambda d: _t2m(d.start))

    # PASO 3: Identificar bloques continuos de 3-10 horas por día
    print("========== [HYB05 POST] ==========")
    print(f"[HYB05_POST] Agrupando demandas híbridas en bloques de 3-10h...")

    # Estructura: {(día, hora_inicio, hora_fin): {puesto: [demandas]}}
    hybrid_blocks: dict[tuple[date, time, time], dict[str, list]] = {}

    MIN_BLOCK_HOURS = 3
    MAX_BLOCK_HOURS = 10
    MIN_BLOCK_MINUTES = MIN_BLOCK_HOURS * 60
    MAX_BLOCK_MINUTES = MAX_BLOCK_HOURS * 60

    # Por cada día, identificar bloques de demandas continuas
    days_with_hybrids = set(
        dm.date for dm in demands if getattr(dm, "is_hybrid_05", False)
    )

    for day in sorted(days_with_hybrids):
        # Obtener todos los puestos que tienen híbridos ese día
        workstations_this_day = set()
        for (d, ws), dms in demands_by_day_ws.items():
            if d == day:
                workstations_this_day.add(ws)

        if len(workstations_this_day) < 2:
            continue  # Necesitamos al menos 2 puestos para formar híbridos

        # Encontrar rangos de tiempo donde TODOS los puestos se solapan
        # Primero, obtener todas las horas donde hay demandas
        all_times = set()
        for ws in workstations_this_day:
            for dm in demands_by_day_ws.get((day, ws), []):
                all_times.add((_t2m(dm.start), _t2m(_tend(dm.end))))

        time_ranges = sorted(all_times)
        if not time_ranges:
            continue

        # Agrupar en bloques continuos
        current_block_start = time_ranges[0][0]
        current_block_end = time_ranges[0][1]

        for start_min, end_min in time_ranges[1:]:
            # ¿Es continuo con el bloque actual? (diferencia <= 15 minutos)
            if start_min - current_block_end <= 15:
                current_block_end = max(current_block_end, end_min)
            else:
                # Terminar bloque actual y empezar uno nuevo
                block_duration = current_block_end - current_block_start
                if MIN_BLOCK_MINUTES <= block_duration <= MAX_BLOCK_MINUTES:
                    # Crear bloque
                    start_time = time(
                        current_block_start // 60, current_block_start % 60
                    )
                    end_time = time(current_block_end // 60, current_block_end % 60)
                    block_key = (day, start_time, end_time)
                    hybrid_blocks[block_key] = {}

                    # Agregar demandas de cada puesto en este rango
                    for ws in workstations_this_day:
                        ws_demands_in_block = []
                        for dm in demands_by_day_ws.get((day, ws), []):
                            dm_start = _t2m(dm.start)
                            dm_end = _t2m(_tend(dm.end))
                            # ¿Esta demanda cae dentro del bloque?
                            if (
                                dm_start >= current_block_start
                                and dm_end <= current_block_end
                            ):
                                ws_demands_in_block.append(dm)

                        if ws_demands_in_block:
                            hybrid_blocks[block_key][ws] = ws_demands_in_block

                # Empezar nuevo bloque
                current_block_start = start_min
                current_block_end = end_min

        # No olvidar el último bloque
        block_duration = current_block_end - current_block_start
        if MIN_BLOCK_MINUTES <= block_duration <= MAX_BLOCK_MINUTES:
            start_time = time(current_block_start // 60, current_block_start % 60)
            end_time = time(current_block_end // 60, current_block_end % 60)
            block_key = (day, start_time, end_time)
            hybrid_blocks[block_key] = {}
            for ws in workstations_this_day:
                ws_demands_in_block = []
                for dm in demands_by_day_ws.get((day, ws), []):
                    dm_start = _t2m(dm.start)
                    dm_end = _t2m(_tend(dm.end))
                    if (
                        dm_start >= current_block_start
                        and dm_end <= current_block_end
                    ):
                        ws_demands_in_block.append(dm)
                if ws_demands_in_block:
                    hybrid_blocks[block_key][ws] = ws_demands_in_block

    print(
        f"[HYB05_POST] Encontrados {len(hybrid_blocks)} bloques de 3-10h con híbridos"
    )

    if not hybrid_blocks:
        print("[HYB05_POST] No se encontraron bloques válidos de 3-10h")
        return

    # PASO 4: Construir uso actual por empleado/día
    used_by_emp_day: dict[str, dict[date, list[tuple[int, int]]]] = defaultdict(
        lambda: defaultdict(list)
    )
    minutes_by_day: dict[str, dict[date, int]] = defaultdict(lambda: defaultdict(int))
    minutes_by_week: dict[str, int] = defaultdict(int)
    days_worked: dict[str, set[date]] = defaultdict(set)

    for day, pairs in sched.items():
        for emp, dm in pairs:
            start_min = _t2m(dm.start)
            end_min = _t2m(_tend(dm.end))
            used_by_emp_day[emp.id][day].append((start_min, end_min))
            minutes_by_day[emp.id][day] += end_min - start_min
            minutes_by_week[emp.id] += end_min - start_min
            if dm.wsid is not None:
                days_worked[emp.id].add(day)

    def _merge_sorted(intervals):
        if not intervals:
            return []
        intervals = sorted(intervals)
        merged = [list(intervals[0])]
        for s, e in intervals[1:]:
            if s <= merged[-1][1]:
                merged[-1][1] = max(merged[-1][1], e)
            else:
                merged.append([s, e])
        return [(a, b) for a, b in merged]

    for eid in list(used_by_emp_day.keys()):
        for d in list(used_by_emp_day[eid].keys()):
            used_by_emp_day[eid][d] = _merge_sorted(used_by_emp_day[eid][d])

    def _fits_daily_caps(emp, day: date, extra_minutes: int) -> bool:
        """
        Verifica que el bloque extra no se pase de:
        - MAX_HOURS_PER_DAY (en horas por día)
        - MAX_DAYS_PER_WEEK (días trabajados a la semana)

        Usa los acumulados locales minutes_by_day y days_worked.
        """
        minutes_today = minutes_by_day[emp.id].get(day, 0)

        # Tope de horas por día
        if minutes_today + extra_minutes > MAX_HOURS_PER_DAY * 60:
            return False

        # Tope de días trabajados en la semana
        days_worked_count = len(days_worked[emp.id])
        inc_day = 0 if minutes_today > 0 else 1
        if days_worked_count + inc_day > MAX_DAYS_PER_WEEK:
            return False

        return True


    # Mapa local: nombre de puesto -> ids reales de Workstation
    wsname_to_ids: dict[str, set] = defaultdict(set)
    for dm in demands:
        if dm.wsid is not None:
            key = (dm.wsname or "").strip().upper()
            wsname_to_ids[key].add(dm.wsid)

    def _can_cover_ws(emp, wsname: str) -> bool:
        if not wsname:
            return False
        key = wsname.strip().upper()

        # Roles directos por Id (WorkstationId en UserWorkstations)
        for wsid in wsname_to_ids.get(key, ()):
            if wsid in emp.roles:
                return True

        # Fallbacks por nombre (JEFE BARRA -> ENLACE, etc.)
        fb_list = (
            ROLE_FALLBACKS_BY_NAME.get(wsname)
            or ROLE_FALLBACKS_BY_NAME.get(wsname.upper())
            or []
        )
        for fb_name in fb_list:
            key_fb = fb_name.strip().upper()
            for wsid in wsname_to_ids.get(key_fb, ()):
                if wsid in emp.roles:
                    return True
        return False

    def _has_overlap(intervals, start_min, end_min):
        for s, e in intervals:
            if not (end_min <= s or start_min >= e):
                return True
        return False

    total_pairs_assigned = 0

    # PASO 5: Asignar cada bloque probando combinaciones de pares
    from itertools import combinations

    for (day, start, end), workstations_dict in sorted(hybrid_blocks.items()):
        block_duration_min = _t2m(end) - _t2m(start)
        block_duration_hours = block_duration_min / 60

        workstation_names = list(workstations_dict.keys())

        if len(workstation_names) < 2:
            print(
                f"[HYB05_POST] Bloque {day} {start}-{end} ({block_duration_hours:.1f}h) solo tiene 1 puesto → omitir"
            )
            continue

        print(
            f"[HYB05_POST] Procesando bloque {day} {start}-{end} "
            f"({block_duration_hours:.1f}h) con {len(workstation_names)} puestos: "
            f"{', '.join(workstation_names)}"
        )

        # Probar todas las combinaciones de pares de puestos
        all_pairs = list(combinations(workstation_names, 2))
        assigned_workstations = set()

        for ws_a, ws_b in all_pairs:
            if ws_a in assigned_workstations or ws_b in assigned_workstations:
                continue  # Ya usamos uno de estos puestos

            # Obtener todas las demandas de estos puestos en el bloque
            demands_a = workstations_dict[ws_a]
            demands_b = workstations_dict[ws_b]

            # Buscar empleado que pueda cubrir AMBOS puestos durante TODO el bloque
            candidatos = []
            debug_counts = {
                "total_emps": len(emps),
                "no_role_a": 0,
                "no_role_b": 0,
                "not_available": 0,
                "overlap": 0,
                "caps": 0,
            }

            start_min = _t2m(start)
            end_min = _t2m(end)

            for emp in emps:
                # Verificar roles
                if not _can_cover_ws(emp, ws_a):
                    debug_counts["no_role_a"] += 1
                    continue
                if not _can_cover_ws(emp, ws_b):
                    debug_counts["no_role_b"] += 1
                    continue

                # Disponibilidad general
                if not emp.available(day, start, end):
                    debug_counts["not_available"] += 1
                    continue

                # ===== NUEVA LÓGICA: PRIORIDAD HÍBRIDOS =====
                # Para híbridos, REASIGNAMOS turnos conflictivos
                # Calculamos cuántas horas usa FUERA del bloque híbrido
                intervals = used_by_emp_day[emp.id].get(day, [])
                has_overlap = _has_overlap(intervals, start_min, end_min)
                
                # Calcular minutos que NO se solapan con el bloque híbrido
                minutes_outside_block = 0
                for int_start, int_end in intervals:
                    # Si no hay solapamiento, contar todos los minutos
                    if int_end <= start_min or int_start >= end_min:
                        minutes_outside_block += (int_end - int_start)
                    # Si hay solapamiento parcial, contar solo la parte que no se solapa
                    else:
                        if int_start < start_min:
                            minutes_outside_block += (start_min - int_start)
                        if int_end > end_min:
                            minutes_outside_block += (int_end - end_min)
                
                if has_overlap:
                    debug_counts["overlap"] += 1
                
                # Verificar límite con las horas recalculadas
                # (minutos fuera del bloque + el bloque híbrido completo)
                total_with_hybrid = minutes_outside_block + block_duration_min
                
                if total_with_hybrid > MAX_HOURS_PER_DAY * 60:
                    debug_counts["caps"] += 1
                    continue
                
                # Verificar días trabajados
                inc_day = 0 if minutes_by_day[emp.id].get(day, 0) > 0 else 1
                if (len(days_worked[emp.id]) + inc_day) > MAX_DAYS_PER_WEEK:
                    debug_counts["caps"] += 1
                    continue

                candidatos.append(
                    (
                        minutes_outside_block,  # Priorizar quien tenga menos horas fuera del bloque
                        minutes_by_week[emp.id],
                        has_overlap,  # Secundario: preferir sin solapamiento
                        emp,
                    )
                )

            if not candidatos:
                print(
                    f"[HYB05_POST] Sin candidato para bloque {day} {start}-{end} "
                    f"{ws_a} + {ws_b} ({block_duration_hours:.1f}h) | "
                    f"Rechazos: no_{ws_a}={debug_counts['no_role_a']}, "
                    f"no_{ws_b}={debug_counts['no_role_b']}, "
                    f"no_disponible={debug_counts['not_available']}, "
                    f"solapamiento={debug_counts['overlap']}, "
                    f"limite_horas={debug_counts['caps']}"
                )
                continue

            # ¡Encontramos candidatos!
            candidatos.sort(key=lambda x: (x[0], x[1], x[2]))  # minutos_fuera, semana, tiene_overlap
            minutes_outside, _, had_overlap, chosen = candidatos[0]
            
            if had_overlap:
                print(f"[HYB05_POST] ⚠️  {chosen.name} tenía solapamiento, reasignando turnos...")

            # Antes de asignar el bloque híbrido, liberamos al empleado
            # de cualquier turno normal que se solape con [start, end]
            sched_day = sched.get(day, [])
            if sched_day:
                new_sched_day = []
                removed_for_chosen: list["Demand"] = []
                for emp2, dm2 in sched_day:
                    if emp2.id == chosen.id:
                        dm2_start = _t2m(dm2.start)
                        dm2_end = _t2m(_tend(dm2.end))
                        if not (dm2_end <= start_min or dm2_start >= end_min):
                            # Se solapa: eliminamos esta asignación previa
                            removed_for_chosen.append(dm2)
                            if dm2.id in coverage_stats:
                                cov = coverage_stats[dm2.id]
                                cov["met"] = max(0, cov.get("met", 0) - 1)
                                cov["unmet"] = cov.get("unmet", 0) + 1
                            continue
                    new_sched_day.append((emp2, dm2))
                sched[day] = new_sched_day

                # Recalcular minutos/intervalos para el empleado elegido ese día
                new_intervals = []
                for emp2, dm2 in new_sched_day:
                    if emp2.id == chosen.id:
                        s2 = _t2m(dm2.start)
                        e2 = _t2m(_tend(dm2.end))
                        new_intervals.append((s2, e2))
                used_by_emp_day[chosen.id][day] = _merge_sorted(new_intervals)
                minutes_by_day[chosen.id][day] = sum(
                    e2 - s2 for s2, e2 in used_by_emp_day[chosen.id][day]
                )
                # Recalcular minutos semanales y días trabajados del elegido
                total_week_minutes = 0
                days_set: set[date] = set()
                for d2, ivals in used_by_emp_day[chosen.id].items():
                    if ivals:
                        days_set.add(d2)
                        for s2, e2 in ivals:
                            total_week_minutes += e2 - s2
                minutes_by_week[chosen.id] = total_week_minutes
                days_worked[chosen.id] = days_set

            # Asignar TODAS las demandas de ambos puestos en el bloque
            for dm in demands_a + demands_b:
                sched.setdefault(day, []).append((chosen, dm))

                # Actualizar coverage
                entry = coverage_stats.get(dm.id)
                if entry is None:
                    entry = {
                        "demand": dm,
                        "met": 0,
                        "unmet": dm.need,
                        "covered": 0,
                        "employees": [],
                    }
                    coverage_stats[dm.id] = entry
                
                # Asegurar que la estructura tenga todas las claves necesarias
                if "employees" not in entry:
                    entry["employees"] = []
                if "met" not in entry:
                    entry["met"] = 0
                if "covered" not in entry:
                    entry["covered"] = 0
                if "unmet" not in entry:
                    entry["unmet"] = dm.need
                
                # Actualizar contadores
                entry["met"] = min(entry.get("met", 0) + 1, dm.need)
                entry["covered"] = entry["met"]
                entry["unmet"] = max(0, dm.need - entry["met"])
                entry["employees"].append(chosen)

            # Actualizar uso del empleado
            used_by_emp_day[chosen.id][day] = _merge_sorted(
                used_by_emp_day[chosen.id][day] + [(start_min, end_min)]
            )
            minutes_by_day[chosen.id][day] += block_duration_min
            minutes_by_week[chosen.id] += block_duration_min
            days_worked[chosen.id].add(day)

            # Marcar puestos como asignados
            assigned_workstations.add(ws_a)
            assigned_workstations.add(ws_b)

            total_pairs_assigned += 1
            
            # Log mejorado con información de reasignación
            if had_overlap:
                removed_count = len([dm for emp2, dm in sched_day if emp2.id == chosen.id 
                                    and not (sched_day and (emp2, dm) in sched.get(day, []))])
                print(
                    f"[HYB05_POST] ✓ Asignado BLOQUE híbrido {day} {start}-{end} ({block_duration_hours:.1f}h) "
                    f"{ws_a} + {ws_b} a {chosen.name} "
                    f"({len(demands_a)} + {len(demands_b)} = {len(demands_a) + len(demands_b)} demandas) "
                    f"[REASIGNÓ: liberó turnos conflictivos]"
                )
            else:
                print(
                    f"[HYB05_POST] ✓ Asignado BLOQUE híbrido {day} {start}-{end} ({block_duration_hours:.1f}h) "
                    f"{ws_a} + {ws_b} a {chosen.name} "
                    f"({len(demands_a)} + {len(demands_b)} = {len(demands_a) + len(demands_b)} demandas)"
                )
            logger.info(
                "[HYB05_POST] Assigned hybrid block %s %s-%s (%.1fh) %s+%s to %s",
                day, start, end, block_duration_hours, ws_a, ws_b, chosen.name
            )

    print(f"[HYB05_POST] total_bloques_asignados={total_pairs_assigned}")


def add_shifttype_must_cover_if_possible(mdl, emps, dem, X, overrides):
    by_date = defaultdict(list)
    for d in dem:
        by_date[d.date].append(d)

    for e in emps:
        for day, day_dems in sorted(by_date.items(), key=lambda kv: kv[0]):
            dow = day.weekday()

            # ── NUEVO: si es 'caso Félix' este día, no exigimos cubrir ST
            if _is_felix_like_day(e, day, overrides):
                if ASCII_LOGS:
                    print(f"[ST-MUST-BYPASS][{day}] {e.name}: dos US-starts y ST no cubre 3h → no forzamos cubrir ST.")
                continue

            st_wins = e.shift_type_windows.get(dow, [])
            if not st_wins:
                continue

            # US enforzado manda; si existe, no forzamos ST aquí (ya estaba)
            if e.user_shift_windows.get(dow) and (e.id, day) not in overrides:
                continue

            mins_inside = 0
            inside_vars = []
            for dm in day_dems:
                if (e.id, dm.id) not in X:
                    continue
                end = dm.end if dm.end != time(0,0) else time(23,59)
                for ws, we in st_wins:
                    if dm.start >= ws and end <= we:
                        mins_inside += duration_min(dm)
                        inside_vars.append(X[e.id, dm.id])
                        break
            if mins_inside >= MIN_SHIFT_DURATION_HOURS * 60 and inside_vars:
                mdl.Add(sum(inside_vars) >= 1)


def _fmt_hhmm(t: time) -> str:
    """Formatea hora HH:MM; tratamos 00:00 como 23:59 por convención de fin de día."""
    if t == time(0, 0):
        return "23:59"
    return f"{t.hour:02d}:{t.minute:02d}"

def _dow_es(i: int) -> str:
    """Nombre corto de día en español (LUN..DOM)."""
    return ["LUN","MAR","MIÉ","JUE","VIE","SÁB","DOM"][i]

def debug_print_usershifts(emps: List['Emp'], week: List[date], usershift_plan: Dict[Tuple[str, date], dict]) -> None:
    """
    Traza por consola, por cada día, qué empleados tienen UserShift y sus ventanas,
    junto con el modo calculado (usershift_enforced | free_mode), los minutos viables
    dentro de ventanas y si es single/split.
    """
    if not ASCII_LOGS:
        return
    print("[USERSHIFT] ───────────── RESUMEN POR DÍA ─────────────")
    for d in week:
        dow = d.weekday()
        print(f"[USERSHIFT] {d.isoformat()} ({_dow_es(dow)})")
        count = 0
        for e in emps:
            wins = e.user_shift_windows.get(dow, [])
            if not wins:
                continue
            count += 1
            spans = " | ".join([
                f"{_fmt_hhmm(s)}-{_fmt_hhmm(we if we != time(0,0) else time(23,59))}"
                for (s, we) in sorted(wins, key=lambda w: (_t2m(w[0]), _t2m(w[1])))
            ])
            entry  = usershift_plan.get((e.id, d), {})
            mode   = entry.get("mode", "free_mode")
            mins   = entry.get("minutes_in_window", 0)
            kind   = entry.get("kind", None)
            reason = entry.get("reason", "ok")
            print(f"[USERSHIFT]  - {e.name}: ventanas [{spans}]  » mode={mode} kind={kind} mins={mins} reason={reason}")
        if count == 0:
            print("[USERSHIFT]  (ningún empleado con UserShift este día)")

def build_latest_end_map_from_demands(demands):
    """
    Devuelve: { date_iso -> { wsid_str -> end_min } }, donde end_min está en minutos.
    Si una demanda termina a 00:00, se interpreta como 23:59 (1439).
    """
    
    latest = defaultdict(dict)
    for dm in demands:
        if dm.wsid is None:
            continue
        end_t = dm.end if dm.end != time(0,0) else time(23,59)
        end_m = _t2m(end_t)
        prev = latest[dm.date].get(dm.wsid, -1)
        if end_m > prev:
            latest[dm.date][dm.wsid] = end_m
    # convertir claves a strings (ISO/str) para serializar
    latest_iso = {d.isoformat(): {str(w): m for w, m in m2.items()} for d, m2 in latest.items()}
    return latest_iso


def build_latest_end_of_day_map(demands):
    """
    Devuelve: { date_iso -> end_min }, donde end_min es la última hora de fin
    considerando TODAS las estaciones/puestos del día. Si alguna demanda termina
    a 00:00, se interpreta como 23:59 (1439).
    """
    latest = {}
    for dm in demands:
        if dm.wsid is None:
            continue
        end_t = dm.end if dm.end != time(0,0) else time(23,59)
        end_m = _t2m(end_t)
        key = dm.date.isoformat() if hasattr(dm.date, 'isoformat') else str(dm.date)
        prev = latest.get(key, -1)
        if end_m > prev:
            latest[key] = end_m
    return latest


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
def split_long_segment(d: date, wsid, wsname, s_min: int, e_min: int, need: int, max_hours: int, raw_need=None):
    """
    Corta [s_min, e_min) en trozos de como máximo max_hours horas,
    pero conservando el EffortRequired original (raw_need) cuando exista.
    Eso evita perder los 0.5 de los puestos híbridos.
    """
    out = []
    limit = max_hours * 60
    cur = s_min

    # Si nos pasan raw_need (por ejemplo 0.5), lo usamos; si no, usamos need.
    eff = need if raw_need is None else raw_need

    while cur < e_min:
        nxt = min(cur + limit, e_min)
        out.append(
            Demand(
                (
                    uid(),
                    d,
                    wsid,
                    wsname,
                    _m2t(cur),
                    _m2t(nxt if nxt < 24 * 60 else 0),
                    eff,
                )
            )
        )
        cur = nxt
    return out


def coalesce_demands(demands, tolerate_gap_min: int = 0):
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
            if (
                nxt.need == curr.need
                and _t2m(nxt.start) - _t2m(curr.end) <= tolerate_gap_min
                and pot_dur_h <= MAX_HOURS_PER_DAY
            ):
                curr.end = nxt.end
            else:
                merged.append(curr)
                curr = nxt
        merged.append(curr)

    # 👇 OJO: usamos raw_need si existe, para NO perder las 0,5
    return [
        Demand(
            (
                d.id,
                d.date,
                d.wsid,
                d.wsname,
                d.start,
                d.end,
                getattr(d, "raw_need", d.need),
            )
        )
        for d in merged
    ]

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
            segs = split_long_segment(
                dm.date,
                dm.wsid,
                dm.wsname,
                a,
                b,
                dm.need,
                max_hours,
                getattr(dm, "raw_need", dm.need),
            )
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
    La estructura del US (single/split) se valida solo por forma (ventanas),
    no por demanda. La demanda mínima se comprueba aparte.
    """
    dow = ddate.weekday()
    wins = sorted(emp.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1])))
    if not wins:
        return False, None, "no_usershift_for_day"

    # fusionar solapes
    merged = []
    for s, e in wins:
        smin, emin = _t2m(s), _t2m(e if e != time(0,0) else time(23,59))
        if not merged or smin > merged[-1][1]:
            merged.append([smin, emin])
        else:
            merged[-1][1] = max(merged[-1][1], emin)

    if len(merged) == 1:
        return True, "single", "ok"
    if len(merged) >= 2:
        a, b = merged[0], merged[1]
        gap = b[0] - a[1]
        if gap >= MIN_HOURS_BETWEEN_SPLIT * 60:
            return True, "split", "ok"
        return False, None, "usershift_split_gap_lt_min"

    return False, None, "usershift_structure_unsupported"


def _minutes_candidate_in_usershift(emp: Emp, ddate: date, demands: List[Demand]) -> Tuple[int, str]:
    """Suma de minutos de demanda dentro de cualquier ventana de US del día.
       Si total >= 3h ⇒ hay volumen para hacer obligatorio el UserShift.
       IMPORTANTE: aquí NO miramos 0–5 ni ShiftTypes; solo ventanas y roles.
    """
    dow = ddate.weekday()
    wins = emp.user_shift_windows.get(dow)
    if not wins:
        return 0, "no_usershift_for_day"

    total = 0
    any_inside = False
    for dm in demands:
        if dm.date != ddate:
            continue
        if not emp.can(dm.wsid):
            continue
        end = dm.end if dm.end != time(0,0) else time(23,59)
        for w_s, w_e in wins:
            w_end = w_e if w_e != time(0,0) else time(23,59)
            if dm.start >= w_s and end <= w_end:
                any_inside = True
                total += duration_min(dm)   # ← ¡aquí se suman los minutos!
                break

    if not any_inside:
        return 0, "no_demands_inside_window"
    if total < MIN_SHIFT_DURATION_HOURS * 60:
        return total, "insufficient_volume_for_3h"
    return total, "ok"

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

# IDs fijos de "Management"."LawRestrictions"
LAW_IDS = {
    "max_hours_per_day":        "feedc36b-debf-4f51-b882-194c3816c4d1",
    "min_hours_between_split":  "1b52f06b-64d9-40a0-bcf5-c922cfc937c2",
    "min_shift_duration_hours": "df056d24-7d3a-416a-949f-3f0b491515e4",  # horas mínimo a trabajar
    "min_hours_between_shifts": "be491f3f-059b-42ed-adc4-331754d85412",
    "min_days_off_per_week":    "756d9660-5101-4673-892b-267b38dc805e",
}

def fetch_law_restrictions_by_id(ids: dict = None) -> dict:
    """
    Lee 'Management.LawRestrictions' usando los UUID directos y devuelve:
    {
      'resolved': {
         'max_hours_per_day': int|None,
         'min_hours_between_split': int|None,
         'min_shift_duration_hours': int|None,
         'min_hours_between_shifts': int|None,
         'min_days_off_per_week': int|None
      },
      'raw': [{'id':str,'description':str,'hours':int|None}, ...]
    }
    """
    ids = ids or LAW_IDS
    id_list = list(ids.values())

    resolved = {
        "max_hours_per_day": None,
        "min_hours_between_split": None,
        "min_shift_duration_hours": None,
        "min_hours_between_shifts": None,
        "min_days_off_per_week": None,
    }
    raw = []

    with conn() as c, c.cursor() as cur:
        # 🔧 Cast explícito del parámetro a uuid[]
        rows = fetchall(cur, '''
            SELECT "Id"::text, "Description", "CantHours"
            FROM "Management"."LawRestrictions"
            WHERE "Id" = ANY(%s::uuid[])
        ''', (id_list,))

    by_id = {
        row[0]: {"description": row[1], "hours": (int(row[2]) if row[2] is not None else None)}
        for row in rows
    }

    for k, uid in ids.items():
        info = by_id.get(uid)
        if info:
            resolved[k] = info["hours"]
            raw.append({"id": uid, "description": info["description"], "hours": info["hours"]})
        else:
            raw.append({"id": uid, "description": None, "hours": None})

    return {"resolved": resolved, "raw": raw}


def assign_days_off_after_assignment(
    emps: Iterable[Any],
    week: List[date],
    sched: Any,
    min_days_off_per_week: int,
) -> Dict[Any, Set[date]]:
    """
    Selecciona días libres por empleado combinando:
      1) RT==0 de BD (día exacto según DOW de la restricción semanal)
      2) Días adicionales necesarios para llegar a 'min_days_off_per_week',
         elegidos por menor tiempo trabajado (minutos asignados), excluyendo ABS/VAC.

    - 'emps': colección de objetos empleado. Se espera que cada 'emp' tenga:
        emp.id                      -> identificador estable
        emp.day_off: set[int]       -> DOWs con RT==0 (0=Lun..6=Dom)
        emp.absent: set[date]       -> días con ausencia (ABS/VAC)
    - 'week': lista de 7 fechas (mon..sun o como uses), misma semana planificada
    - 'sched': estructura del plan ya asignado (solver/greedy). Soportamos varios formatos.
    - 'min_days_off_per_week': N de la tabla LawRestrictions

    Devuelve: { emp.id : set({date,...}) }
    """
    # --- 0) helpers internos -----------------------------------------------
    def _is_time_like(x) -> bool:
        return isinstance(x, time) or (isinstance(x, datetime))

    def _to_minutes(t: time | datetime) -> int:
        if isinstance(t, datetime):
            return t.hour * 60 + t.minute
        return t.hour * 60 + t.minute

    def _block_minutes(start: Any, end: Any) -> int:
        # Bloque start/end -> minutos (robusto a time/datetime)
        if not (_is_time_like(start) and _is_time_like(end)):
            return 0
        sm, em = _to_minutes(start), _to_minutes(end)
        if em <= sm:
            em += 24 * 60  # tolera cruces raros 00:00
        return max(0, em - sm)

    # --- 1) extraer minutos asignados por (emp_id, date) --------------------
    # Soportamos varios "shapes" comunes de sched para no romper integración.
    minutes_by_emp_date: Dict[Tuple[Any, date], int] = defaultdict(int)

    def _ingest_tuple_key_map(m: Dict[Tuple[Any, date], Any]):
        # m[(emp_id, date)] = list[(start,end)] | list[dict] | ...
        for (uid, d), blocks in m.items():
            total = 0
            if isinstance(blocks, list):
                for b in blocks:
                    if isinstance(b, tuple) and len(b) >= 2:
                        total += _block_minutes(b[0], b[1])
                    elif isinstance(b, dict):
                        s = b.get('start') or b.get('s') or b.get('from')
                        e = b.get('end')   or b.get('e') or b.get('to')
                        total += _block_minutes(s, e)
            minutes_by_emp_date[(uid, d)] += total

    def _ingest_flat_list(lst: List[Any]):
        # lst = [ { user_id/employee_id, date, start, end }, ... ]
        for rec in lst:
            if not isinstance(rec, dict):
                continue
            uid = rec.get('user_id') or rec.get('employee_id') or rec.get('emp_id') or rec.get('uid')
            d   = rec.get('date') or rec.get('day') or rec.get('fecha')
            s   = rec.get('start') or rec.get('s') or rec.get('from')
            e   = rec.get('end')   or rec.get('e') or rec.get('to')
            if isinstance(d, str):
                try:
                    d = datetime.fromisoformat(d).date()
                except Exception:
                    # Si viene como 'YYYY-MM-DD' simple:
                    try:
                        y, m, dd = d.split('-')
                        d = date(int(y), int(m), int(dd))
                    except Exception:
                        d = None
            if uid is not None and isinstance(d, date):
                minutes_by_emp_date[(uid, d)] += _block_minutes(s, e)

    # Detecta forma de 'sched'
    if hasattr(sched, 'emp_day_minutes') and isinstance(sched.emp_day_minutes, dict):
        # Caso A: ya trae minutos por (uid, date)
        for (uid, d), minutes in sched.emp_day_minutes.items():
            minutes_by_emp_date[(uid, d)] += int(minutes or 0)

    elif isinstance(sched, dict):
        # Caso B1: dict interno conocido
        if 'emp_day_minutes' in sched and isinstance(sched['emp_day_minutes'], dict):
            for (uid, d), minutes in sched['emp_day_minutes'].items():
                minutes_by_emp_date[(uid, d)] += int(minutes or 0)
        # Caso B2: mapas por tupla (emp_id, date) -> [bloques]
        elif any(isinstance(k, tuple) and len(k) == 2 for k in sched.keys()):
            _ingest_tuple_key_map(sched)
        # Caso B3: subconjuntos comunes
        elif 'by_emp_date' in sched and isinstance(sched['by_emp_date'], dict):
            _ingest_tuple_key_map(sched['by_emp_date'])
        elif 'assignments' in sched and isinstance(sched['assignments'], list):
            _ingest_flat_list(sched['assignments'])

    elif isinstance(sched, list):
        # Caso C: lista plana de asignaciones
        _ingest_flat_list(sched)

    # --- 2) construir selección de días libres ------------------------------
    out: Dict[Any, Set[date]] = {}
    week_set = set(week)

    for emp in emps:
        uid = getattr(emp, 'id', getattr(emp, 'Id', None))
        if uid is None:
            # si no hay id visible, usamos el objeto como clave (no deseable, pero seguro)
            uid = emp

        # RT==0 definidos en BD -> “preseleccionados”
        rt0_dows: Set[int] = set(getattr(emp, 'day_off', set()) or set())
        preselected_rt0: Set[date] = {d for d in week if d.weekday() in rt0_dows}

        # ABS/VAC para excluir de la parte "elegida por menor tiempo"
        abs_days: Set[date] = set(getattr(emp, 'absent', set()) or set())

        # Número requerido por ley
        N = int(min_days_off_per_week or 0)

        chosen: Set[date] = set(preselected_rt0) & week_set  # sólo los de la semana
        k = len(chosen)

        # Si faltan “libres” para llegar a N, elegir por menor trabajo (excluye ABS/VAC y RT==0)
        if k < N:
            need = N - k
            # candidatos: días de la semana que no estén ya elegidos ni sean ABS/VAC
            candidates: List[Tuple[int, date]] = []
            for d in week:
                if d in chosen or d in abs_days:
                    continue
                # minutos trabajados ese día:
                minutes = minutes_by_emp_date.get((uid, d), 0)
                candidates.append((minutes, d))
            # ordenar por (minutos asc, día asc)
            candidates.sort(key=lambda t: (t[0], t[1]))
            for _, d in candidates[:need]:
                chosen.add(d)

        # NOTA: si k > N, mantenemos todos los RT==0 (la BD manda).
        out[uid] = chosen

    return out


def load_data(week_start: date):
    week = [week_start + timedelta(days=i) for i in range(7)]
    week_end = week[-1]

    # -------------------------------
    # Helpers locales
    # -------------------------------
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
        ivs = [p for p in blocks if p]
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
        out, cur = [], DAY_START
        for s, e in merged:
            if cur < s:
                out.append((cur, (s if s != time(0, 0) else time(23, 59))))
            cur = max(cur, e)
        if cur < DAY_END:
            out.append((cur, DAY_END))
        return out

    def _merge_windows(blocks):
        """Une intervalos [s,e) que se solapan, para usar en estimación de carga."""
        ivs = [(s, e if e != time(0, 0) else time(23, 59)) for (s, e) in blocks if s and e and s < (e if e != time(0, 0) else time(23, 59))]
        ivs.sort(key=lambda p: (p[0], p[1]))
        merged = []
        for s, e in ivs:
            if not merged or s > merged[-1][1]:
                merged.append([s, e])
            else:
                merged[-1][1] = max(merged[-1][1], e)
        return [(a, b) for (a, b) in merged]

    def _dm_minutes(dm):
        ee = dm.end if dm.end != time(0, 0) else time(23, 59)
        return max(0, _t2m(ee) - _t2m(dm.start))

    def _inside_any(dm_start: time, dm_end: time, wins: list[tuple[time, time]]) -> bool:
        """¿El segmento demanda [dm_start, dm_end] cabe en alguna ventana?"""
        dm_end = dm_end if dm_end != time(0, 0) else time(23, 59)
        for ws, we in wins:
            we = we if we != time(0, 0) else time(23, 59)
            if ws <= dm_start and dm_end <= we:
                return True
        return False

    def _windows_for_date(emp, ddate: date) -> list[tuple[time, time]]:
        """Ventanas disponibles del empleado para ese día (US si existen; de lo contrario weekly/ST; más excepciones de fecha)."""
        dow = ddate.weekday()
        wins = list(emp.user_shift_windows.get(dow, []))
        if not wins:
            wins = list(emp.window.get(dow, [])) + list(emp.shift_type_windows.get(dow, []))
        wins += emp.exc.get(ddate, [])
        return _merge_windows(wins)

    def _dow_es(dow: int) -> str:
        return ['Lun','Mar','Mié','Jue','Vie','Sáb','Dom'][dow % 7]

    with conn() as c, c.cursor() as cur:
        # (0) LEYES por UUID → setear constantes globales
        global MIN_HOURS_BETWEEN_SPLIT, MIN_HOURS_BETWEEN_SHIFTS, MAX_HOURS_PER_DAY, MIN_SHIFT_DURATION_HOURS

        laws = fetch_law_restrictions_by_id()
        L = laws["resolved"] if laws else {}

        # Fallbacks
        _fallback_max_day = 9
        _fallback_min_split = 3
        _fallback_min_shift = 3
        _fallback_min_between_shifts = 12  # 12h entre turnos

        MAX_HOURS_PER_DAY         = int(L.get("max_hours_per_day")         or _fallback_max_day)
        MIN_HOURS_BETWEEN_SPLIT   = int(L.get("min_hours_between_split")   or _fallback_min_split)
        MIN_SHIFT_DURATION_HOURS  = int(L.get("min_hours_duration_hours")  or L.get("min_hours_duration") or L.get("min_hours_per_shift") or _fallback_min_shift)
        MIN_HOURS_BETWEEN_SHIFTS  = int(L.get("min_hours_between_shifts")  or _fallback_min_between_shifts)

        # De BD (2 en tu tabla)
        MIN_DAYS_OFF_PER_WEEK     = int(L.get("min_days_off_per_week")     or 2)

        if ASCII_LOGS:
            print(f"[LAW/UUID] MAX_HOURS_PER_DAY={MAX_HOURS_PER_DAY}h, "
                  f"MIN_SHIFT_DURATION_HOURS={MIN_SHIFT_DURATION_HOURS}h, "
                  f"MIN_HOURS_BETWEEN_SPLIT={MIN_HOURS_BETWEEN_SPLIT}h, "
                  f"MIN_HOURS_BETWEEN_SHIFTS={MIN_HOURS_BETWEEN_SHIFTS}h, "
                  f"MIN_DAYS_OFF_PER_WEEK={MIN_DAYS_OFF_PER_WEEK}")

        # 1) Plantilla y demandas
        tpl_id, tpl_name = pick_template(cur, week_start, week_end)
        print(f"[DEBUG] Template seleccionado: ID={tpl_id}, Name={tpl_name}")

        raw_demands = fetchall(
            cur,
            '''
            SELECT d."Day", w."Name", d."StartTime", d."EndTime", d."TemplateId"
            FROM "Management"."WorkstationDemands" d
            JOIN "Management"."Workstations" w ON w."Id" = d."WorkstationId"
            WHERE d."TemplateId" = %s AND d."Day" = 0
            ORDER BY d."StartTime"
            ''',
            (tpl_id,),
        )
        print(f"[DEBUG] Demandas del lunes en BD para template {tpl_id}:")
        for row in raw_demands:
            print(f"  {row[1]} {row[2]}-{row[3]}")

        min_hours_required = 0  # Horas mínimas semana (se conserva tu lectura por LIKE)

        demands = [
            Demand(r)
            for r in fetchall(
                cur,
                '''
                SELECT d."Id", %s + d."Day"*interval '1 day',
                       d."WorkstationId", w."Name",
                       (TIMESTAMP '2000-01-01'+d."StartTime")::time,
                       (TIMESTAMP '2000-01-01'+d."EndTime")::time,
                       d."EffortRequired"
                FROM "Management"."WorkstationDemands" d
                JOIN "Management"."Workstations"       w ON w."Id" = d."WorkstationId"
                WHERE d."TemplateId" = %s
                ORDER BY d."Day", d."StartTime", d."EndTime", d."Id"
                ''',
                (week_start, tpl_id),
            )
        ]
        demands = coalesce_demands(demands, tolerate_gap_min=0)
        demands = normalize_by_max_need_profile(demands)

        # 2) Empleados y roles
        emps_map = {
            r[0]: Emp(r)
            for r in fetchall(
                cur,
                '''
                SELECT "Id", COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                       COALESCE("ComplementHours", TRUE)
                FROM "Management"."AspNetUsers"
                WHERE "IsActive" AND NOT "IsDelete"
                ORDER BY "LastName","FirstName","Id"
                ''',
            )
        }
        if not emps_map:
            raise DataNotFoundError("No hay empleados activos")

        for uid2, ws in fetchall(
            cur,
            '''
            SELECT "UserId","WorkstationId"
            FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete"
            ORDER BY "UserId","WorkstationId"
            ''',
        ):
            if uid2 in emps_map:
                emps_map[uid2].roles.add(ws)

        if not any(e.roles for e in emps_map.values()):
            raise DataNotFoundError("Ningún empleado tiene roles asignados")

        emps = [emps_map[k] for k in sorted(emps_map.keys())]

        # === 2.a) AUSENTISMOS (HARD BLOCK)
        for uid_abs, sd_abs, ed_abs in fetchall(
            cur,
            '''
            SELECT "UserId",
                   "StartDate"::date,
                   COALESCE("EndDate"::date, %s)
            FROM "Management"."UserAbsenteeisms"
            WHERE "StartDate"::date <= %s
              AND COALESCE("EndDate"::date, %s) >= %s
            ORDER BY "UserId","StartDate","EndDate"
            ''',
            (week_end, week_end, week_end, week_start),
        ):
            if uid_abs not in emps_map:
                continue
            emp = emps_map[uid_abs]
            d0 = max(sd_abs, week_start)
            while d0 <= ed_abs:
                emp.absent.add(d0)
                emp.abs_reason[d0] = 'ABS'
                emp.exc[d0] = []
                d0 += timedelta(days=1)

        if ASCII_LOGS:
            cnt_abs = sum(1 for e in emps_map.values() if any(d in week for d in e.absent))
            if cnt_abs:
                print(f"[ABSENTEEISMS] Empleados con ausentismos en semana: {cnt_abs}")

        # Fallbacks de roles por nombre (expansión)
        name2id = {}
        for _dm in demands:
            name2id[_dm.wsname.upper()] = _dm.wsid
        fallbacks_by_id = {}
        for _src_name, _tgts in ROLE_FALLBACKS_BY_NAME.items():
            _src = name2id.get(_src_name.upper())
            if _src is None:
                continue
            _ids = []
            for _t in _tgts:
                _tid = name2id.get(_t.upper())
                if _tid is not None:
                    _ids.append(_tid)
            if _ids:
                fallbacks_by_id[_src] = _ids
        for _e in emps:
            _e.roles_originales = set(_e.roles)
            for _r in list(_e.roles):
                for _tgt in fallbacks_by_id.get(_r, []):
                    _e.roles.add(_tgt)

        # 3) Restricciones semanales (0–5)
        for uid3, dow, rt, f1, t1, b1s, b1e, b2s, b2e in fetchall(
            cur,
            '''
            SELECT "UserId","DayOfWeek","RestrictionType",
                   "AvailableFrom","AvailableUntil",
                   "Block1Start","Block1End",
                   "Block2Start","Block2End"
            FROM "Management"."EmployeeScheduleRestrictions"
            ORDER BY "UserId","DayOfWeek","RestrictionType"
            ''',
        ):
            if uid3 not in emps_map:
                continue
            emp = emps_map[uid3]
            if rt == 0:
                emp.day_off.add(dow); continue
            if rt == 1:
                emp.window[dow].append((time(0, 0), time(23, 59))); continue
            if rt == 2:
                s = _to_time(f1); e = _to_time(t1)
                if s is None and e is None: continue
                if s is not None and e is None: e = time(23, 59)
                if s is None and e is not None: s = time(0, 0)
                if e == time(0, 0): e = time(23, 59)
                if s < e: emp.window[dow].append((s, e))
                continue
            if rt == 3:
                t = _to_time(t1)
                if t: emp.window[dow].append((time(0, 0), t if t != time(0, 0) else time(23, 59)))
                continue
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

        # INFO descanso por RT==0
        week_dows = {d.weekday() for d in week}
        for e in emps:
            has_rt0 = any((dow in e.day_off) for dow in week_dows)
            e.has_rt0_this_week = has_rt0
            e.rest_exempt_from_additional = bool(has_rt0)
            e.rest_exempt_dates = {d for d in week if d.weekday() in e.day_off} if has_rt0 else set()
            if ASCII_LOGS and has_rt0:
                dow_names = ", ".join(sorted({_dow_es(d.weekday()) for d in e.rest_exempt_dates}))
                print(f"[REST-EXEMPT] {e.name}: tiene RT=0 en semana ({dow_names}) → cuentan como libres.")

        # 4) Excepciones y licencias
        for uid4, d_exc, rt, f, t in fetchall(
            cur,
            '''
            SELECT "UserId","Date","RestrictionType",
                   "AvailableFrom","AvailableUntil"
            FROM "Management"."EmployeeScheduleExceptions"
            WHERE "Date" BETWEEN %s AND %s
            ORDER BY "UserId","Date","RestrictionType"
            ''',
            (week_start, week_end),
        ):
            if uid4 not in emps_map:
                continue
            emp = emps_map[uid4]
            if rt == 0:
                emp.absent.add(d_exc)
                emp.abs_reason[d_exc] = 'VAC' if emp.abs_reason.get(d_exc) != 'ABS' else emp.abs_reason.get(d_exc, 'ABS')
            else:
                s = _to_time(f); e = _to_time(t)
                if s and e and s < e:
                    if e == time(0, 0): e = time(23, 59)
                    emp.exc[d_exc].append((s, e))

        for uid5, sd, ed in fetchall(
            cur,
            '''
            SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
            FROM "Management"."Licenses"
            WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
            ORDER BY "UserId","StartDate","EndDate"
            ''',
            (week_end, week_end, week_end, week_start),
        ):
            if uid5 not in emps_map: continue
            emp = emps_map[uid5]
            d0 = max(sd, week_start)
            while d0 <= ed:
                emp.absent.add(d0); emp.abs_reason[d0] = 'VAC'
                d0 += timedelta(days=1)

        # 5) ShiftTypes y restricciones por ST
        shift_types = []
        for row in fetchall(
            cur,
            '''
            SELECT "Id","Name","Description",
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time AS start_time,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time AS end_time,
                   "Structure" = 1 AS is_split,
                   (TIMESTAMP '2000-01-01' + COALESCE("Block2Start",      INTERVAL '00:00:00'))::time AS b2_start,
                   (TIMESTAMP '2000-01-01' + COALESCE("Block2lastStart",  INTERVAL '00:00:00'))::time AS b2_end,
                   "IsActive"
            FROM "Management"."ShiftTypes"
            WHERE "IsActive" = TRUE
            ORDER BY "Name","Id"
            ''',
        ):
            shift_types.append(
                {
                    'id': row[0], 'name': row[1], 'description': row[2],
                    'start_time': row[3], 'end_time': row[4],
                    'is_split': row[5], 'b2_start': row[6], 'b2_end': row[7],
                    'is_active': row[8],
                }
            )
        shift_types_by_id = {st['id']: st for st in shift_types}

        for uidX, dowX, stid in fetchall(
            cur,
            '''
            SELECT "UserId","DayOfWeek","ShiftTypeId"
            FROM "Management"."EmployeeShiftTypeRestrictions"
            ORDER BY "UserId","DayOfWeek","ShiftTypeId"
            ''',
        ):
            if uidX not in emps_map or stid not in shift_types_by_id: continue
            emp = emps_map[uidX]; st = shift_types_by_id[stid]
            emp.shift_type_restr_by_dow[dowX].add(stid)

            def _cap(t: time) -> time:
                return t if t != time(0, 0) else time(23, 59)

            if st['start_time'] and st['end_time'] and st['start_time'] < _cap(st['end_time']):
                emp.shift_type_windows[dowX].append((st['start_time'], _cap(st['end_time'])))
            if st['is_split'] and st.get('b2_start') and st.get('b2_end') and st['b2_start'] < _cap(st['b2_end']):
                emp.shift_type_windows[dowX].append((st['b2_start'], _cap(st['b2_end'])))

        # 6) UserShifts → construir ventanas
        def _cap_end_from_start(start_t: time, candidate_end: time | None) -> time:
            end_eff = candidate_end or time(23, 59)
            if end_eff == time(0, 0): end_eff = time(23, 59)
            end_m = min(_t2m(end_eff), _t2m(start_t) + MAX_HOURS_PER_DAY * 60)
            return _m2t(end_m if end_m < 24 * 60 else 0)

        def _plus_minutes(t: time, minutes: int) -> time:
            return _m2t(min(_t2m(t) + minutes, 24 * 60 - 1))

        MIN_BLOCK_MIN = MIN_SHIFT_DURATION_HOURS * 60
        GAP_MIN       = MIN_HOURS_BETWEEN_SPLIT * 60
        DAY_MAX_MIN   = MAX_HOURS_PER_DAY * 60

        us_rows = fetchall(
            cur,
            '''
            SELECT "UserId","Day","Structure",
                   (TIMESTAMP '2000-01-01' + "Block1Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block1lastStart")::time,
                   (TIMESTAMP '2000-01-01' + "Block2Start")::time,
                   (TIMESTAMP '2000-01-01' + "Block2lastStart")::time
            FROM "Management"."UserShifts"
            ORDER BY "UserId","Day","Block1Start","Block2Start"
            ''',
        )

        groups = defaultdict(list)
        for uid7, day, structure, b1s, b1e, b2s, b2e in us_rows:
            groups[(uid7, day)].append((structure, b1s, b1e, b2s, b2e))

        for e in emps:
            e.has_us_row_by_dow = defaultdict(bool)
            e.no_assign_by_date = set()

        for (uid7, day), rows in groups.items():
            if uid7 not in emps_map: continue
            emp = emps_map[uid7]
            emp.has_us_row_by_dow[day] = True
            windows: list[tuple[time, time]] = []

            b1_starts = [r[1] for r in rows if r[1] is not None]
            b1_ends   = [r[2] for r in rows if r[2] is not None]
            b2_any    = any(r[3] is not None or r[4] is not None for r in rows)
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
                for ws, we in windows:
                    if ws < we:
                        emp.user_shift_windows[day].append((ws, we))
                emp.us_two_starts_dow.add(day)
            else:
                for structure, b1s, b1e, b2s, b2e in rows:
                    b1e = b1e if b1e != time(0, 0) else time(23, 59) if b1e else None
                    b2e = b2e if b2e != time(0, 0) else time(23, 59) if b2e else None
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

                    for ws, we in local_wins:
                        if ws < we:
                            emp.user_shift_windows[day].append((ws, we))
                    if b1s and b2s: emp.us_two_starts_dow.add(day)

        # CASO E: día SIN UserShift → desde ST
        for e in emps:
            for dow in range(7):
                if e.user_shift_windows.get(dow):
                    continue
                raw = e.shift_type_windows.get(dow, [])
                wins = sorted(list({(w[0], w[1]) for w in raw}), key=lambda w: _t2m(w[0]))
                if not wins: continue
                GAP_MIN = MIN_HOURS_BETWEEN_SPLIT * 60
                DAY_MAX_MIN = MAX_HOURS_PER_DAY * 60
                MIN_BLOCK_MIN = MIN_SHIFT_DURATION_HOURS * 60
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
                if ASCII_LOGS:
                    dn = ['Lun','Mar','Mié','Jue','Vie','Sáb','Dom'][dow]
                    print(f"[USERSHIFT/CASE-E-ST] {e.name} {dn}: ventanas={e.user_shift_windows.get(dow)}")

        # 6.a*) PRE-REGLA INTER-JORNADA (OBLIGATORIA)
        #      Si D→D+1 < MIN_HOURS_BETWEEN_SHIFTS:
        #        - con US real en D+1 ⇒ BLOQUEAR D+1 (no asigna, cuenta como descanso)
        #        - sin US real en D+1 ⇒ recortar ventanas para comenzar luego del mínimo legal
        NEED_REST_MIN = MIN_HOURS_BETWEEN_SHIFTS * 60

        def _clip_after_min_start(_wins: list[tuple[time, time]], _needed_min_start: int) -> list[tuple[time, time]]:
            _out: list[tuple[time, time]] = []
            for _s, _e in _wins:
                _e2 = _e if _e != time(0, 0) else time(23, 59)
                _s2m = max(_t2m(_s), _needed_min_start)
                if _s2m < _t2m(_e2):
                    _out.append((_m2t(_s2m), _e2))
            return _out

        for _e in emps:
            for _i in range(len(week) - 1):
                _d = week[_i]
                _d_next = week[_i + 1]

                # Si alguno de los días es descanso/ausencia, no intervenimos
                if _e.off(_d) or _e.absent_day(_d) or _e.off(_d_next) or _e.absent_day(_d_next):
                    continue

                _wins_d = _windows_for_date(_e, _d)
                _wins_n = _windows_for_date(_e, _d_next)
                if not _wins_d or not _wins_n:
                    continue

                _max_end_d = max(_t2m(_we if _we != time(0, 0) else time(23, 59)) for _, _we in _wins_d)
                _min_start_n = min(_t2m(_ws) for _ws, _ in _wins_n)
                _rest_gap = (24 * 60 - _max_end_d) + _min_start_n

                if _rest_gap < NEED_REST_MIN:
                    _needed_start_min = max(_min_start_n, max(0, _max_end_d + NEED_REST_MIN - 24 * 60))
                    _dow_next = _d_next.weekday()

                    if _e.has_us_row_by_dow.get(_dow_next, False):
                        # >>>>>>>>> CAMBIO: US real en D+1 ⇒ BLOQUEAR COMPLETO EL DÍA
                        _e.no_assign_by_date.add(_d_next)
                        _e.user_shift_windows[_dow_next] = []
                        _e.shift_type_windows[_dow_next] = []
                        _e.window[_dow_next] = []
                        _e.exc[_d_next] = []
                        if ASCII_LOGS:
                            print(f"[INTER-JORNADA/US-BLOCK] {_e.name} {_d_next} "
                                  f"gap={_rest_gap}min < {NEED_REST_MIN}min ⇒ día bloqueado (cuenta como descanso).")
                    else:
                        # Sin US real ⇒ recortamos todas las fuentes del D+1
                        if _e.user_shift_windows.get(_dow_next):
                            _e.user_shift_windows[_dow_next] = _clip_after_min_start(_e.user_shift_windows[_dow_next], _needed_start_min)
                        if _e.window.get(_dow_next):
                            _e.window[_dow_next] = _clip_after_min_start(_e.window[_dow_next], _needed_start_min)
                        if _e.shift_type_windows.get(_dow_next):
                            _e.shift_type_windows[_dow_next] = _clip_after_min_start(_e.shift_type_windows[_dow_next], _needed_start_min)
                        if _e.exc.get(_d_next):
                            _e.exc[_d_next] = _clip_after_min_start(_e.exc[_d_next], _needed_start_min)

        # 6.b) Ancla por día + ENFORCE US (salta días con ABS)
        for e in emps:
            e.user_shift_anchor_by_date = {}
            for ddate in week:
                if e.absent_day(ddate):
                    if ASCII_LOGS:
                        print(f"[ANCHOR/SKIP-ABS] {e.name} {ddate} → AUSENTE (ABS/VAC); no se evalúa ancla.")
                    continue

                dow = ddate.weekday()
                wins = e.user_shift_windows.get(dow, [])
                if not wins:
                    if ASCII_LOGS:
                        print(f"[ANCHOR] {e.name} {ddate} → sin ventanas US; no hay ancla.")
                    continue

                earliest_min = None; earliest_dm = None
                for dm in demands:
                    if dm.date != ddate: continue
                    if not e.can(dm.wsid): continue
                    dm_end = dm.end if dm.end != time(0, 0) else time(23, 59)
                    inside = any(dm.start >= ws and dm_end <= (we if we != time(0, 0) else time(23, 59)) for (ws, we) in wins)
                    if not inside: continue
                    st_min = _t2m(dm.start)
                    if earliest_min is None or st_min < earliest_min:
                        earliest_min = st_min; earliest_dm = dm

                if earliest_min is not None:
                    e.user_shift_anchor_by_date[ddate] = _m2t(earliest_min)
                    if ASCII_LOGS:
                        print(f"[ANCHOR] {e.name} {ddate} → ancla {_m2t(earliest_min).strftime('%H:%M')} "
                              f"(ws='{earliest_dm.wsname}', seg={earliest_dm.start.strftime('%H:%M')}-{earliest_dm.end.strftime('%H:%M')})")
                else:
                    if e.has_us_row_by_dow.get(dow, False):
                        # US real pero sin horas válidas: bloquear día (cuenta como descanso)
                        e.no_assign_by_date.add(ddate)
                        e.user_shift_windows[dow] = []
                        e.shift_type_windows[dow] = []
                        e.window[dow] = []
                        e.exc[ddate] = []
                        if ASCII_LOGS:
                            print(f"[US-BLOCK] {e.name} {ddate} → US sin horas válidas; se bloquea el día y cuenta como descanso.")
                    else:
                        if ASCII_LOGS:
                            print(f"[ANCHOR] {e.name} {ddate} → ventanas (p.e. por ST) sin demanda; no se aplica US-ENFORCE.")

        # -------------------------------
        # 6.c) Política EXACTA de días libres (menor carga esperada)
        # -------------------------------
        demands_by_date: dict[date, list] = defaultdict(list)
        for dm in demands:
            demands_by_date[dm.date].append(dm)

        def _expected_minutes(emp, ddate: date) -> int:
            if emp.absent_day(ddate):
                return 0
            wins = _windows_for_date(emp, ddate)
            if not wins:
                return 0
            mins = 0
            for dm in demands_by_date.get(ddate, []):
                if not emp.can(dm.wsid):
                    continue
                dm_end = dm.end if dm.end != time(0, 0) else time(23, 59)
                if _inside_any(dm.start, dm_end, wins):
                    mins += _dm_minutes(dm)
            return mins

        forced_free_by_emp = {}
        for e in emps:
            rt0_dates = {d for d in week if d.weekday() in e.day_off}
            abs_vac_dates = {d for d in week if e.absent_day(d) and e.abs_reason.get(d) in ('ABS', 'VAC')}
            na_dates = {d for d in week if d in e.no_assign_by_date}

            baseline_rest = rt0_dates | abs_vac_dates | na_dates
            needed = max(0, MIN_DAYS_OFF_PER_WEEK - len(baseline_rest))

            if needed <= 0:
                forced_free_by_emp[e.id] = []
                e.forced_free_dates = set()
                if ASCII_LOGS and baseline_rest:
                    print(f"[FORCED-FREE/SKIP] {e.name} ya cumple libres con RT0/ABS/VAC/NA → needed=0")
                continue

            def has_us_real(day: date) -> bool:
                return bool(e.has_us_row_by_dow.get(day.weekday(), False))

            tier1 = [d for d in week
                     if (d.weekday() not in e.day_off)
                     and (not e.window.get(d.weekday()))
                     and (not has_us_real(d))
                     and (not e.absent_day(d))
                     and (d not in baseline_rest)]

            tier2 = [d for d in week
                     if (d not in tier1)
                     and (d.weekday() not in e.day_off)
                     and (not has_us_real(d))
                     and (not e.absent_day(d))
                     and (d not in baseline_rest)]

            tier3 = [d for d in week
                     if (d not in tier1 and d not in tier2)
                     and (d.weekday() not in e.day_off)
                     and (not e.absent_day(d))
                     and (d not in baseline_rest)]

            chosen = []
            for pool in (tier1, tier2, tier3):
                if not pool:
                    continue
                sorted_pool = sorted(
                    pool,
                    key=lambda di: (_expected_minutes(e, di), di.toordinal())
                )
                for d in sorted_pool:
                    if len(chosen) >= needed:
                        break
                    chosen.append(d)
                if len(chosen) >= needed:
                    break

            for d in chosen:
                dw = d.weekday()
                e.user_shift_windows[dw] = []
                e.shift_type_windows[dw] = []
                e.has_us_row_by_dow[dw] = False
                e.window[dw] = []
                e.exc[d] = []
                if ASCII_LOGS:
                    mins = _expected_minutes(e, d)
                    print(f"[FORCED-FREE] {e.name} {d.isoformat()} ({_dow_es(dw)}) → LIBRE forzado "
                          f"(mins_esperados={mins}, pool={'1' if d in tier1 else '2' if d in tier2 else '3'})")

            e.forced_free_dates = set(chosen)
            forced_free_by_emp[e.id] = [d.isoformat() for d in chosen]

        # 7) Ley: horas mín. semana (LIKE)
        row = fetchall(
            cur,
            '''
            SELECT "CantHours" FROM "Management"."LawRestrictions"
            WHERE LOWER("Description") LIKE %s AND "CantHours" IS NOT NULL LIMIT 1
            ''',
            ('%horas minimo%',),
        )
        if row:
            min_hours_required = int(row[0][0])
            if ASCII_LOGS:
                print(f"[LAW] Horas mínimas por semana: {min_hours_required}")

        # 8) Cortes por bordes de UserShift
        extra_cuts_by_date = build_extra_cuts_from_usershifts_edges_only(emps_map, week)
        if ASCII_LOGS:
            dbg = {d.isoformat(): sorted(list(v))[:10] for d, v in extra_cuts_by_date.items()}
            print("[DEBUG] extra cuts (muestra):", dbg)

        demands = normalize_with_extra_cuts(demands, extra_cuts_by_date, max_hours=MAX_HOURS_PER_DAY)
        demands = squash_micro_segments(demands, MIN_SEGMENT_MINUTES)

        # 9) ShiftType por demanda + slot index
        for dm in demands:
            dm.shift_type = get_shifttype_for_demand(dm, shift_types)
        set_slot_indexes(demands)

        if not demands:
            raise DataNotFoundError("La plantilla seleccionada no tiene demandas")

    # Meta debugging/reportes
    rest_policy_meta = {
        "rest_exempt_emp_ids": [e.id for e in emps if getattr(e, "rest_exempt_from_additional", False)],
        "rest_exempt_dates_by_emp": {
            e.id: sorted([d.isoformat() for d in getattr(e, "rest_exempt_dates", set())])
            for e in emps if getattr(e, "rest_exempt_from_additional", False)
        },
        "abs_or_vac_by_emp": {
            e.id: sorted([d.isoformat() for d in week if e.absent_day(d) and e.abs_reason.get(d) in ('ABS','VAC')])
            for e in emps
        },
        "forced_free_by_emp": forced_free_by_emp,
        "policy_note": (
            "Política L-D: exactamente MIN_DAYS_OFF_PER_WEEK por persona; "
            "RT==0, ABS/VAC y US no asignable (NA) cuentan como descanso; "
            "y la inter-jornada es jerárquicamente superior a UserShift."
        )
    }

    return emps, demands, tpl_name, week, rest_policy_meta, shift_types, min_hours_required


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
    """
    Si el día NO está en override y el empleado tiene ventanas de UserShift:
      - Obliga a cubrir al menos UNA demanda TOTALMENTE DENTRO de CADA ventana.
    """
    if not HARD_REQUIRE_USERSHIFT:
        return

    by_date = defaultdict(list)
    for d in dem:
        by_date[d.date].append(d)

    for e in emps:
        for day, day_dems in sorted(by_date.items(), key=lambda kv: kv[0]):
            if (e.id, day) in overrides:
                continue  # libre → no obligar
            dow = day.weekday()
            wins = sorted(e.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1])))
            if not wins:
                continue

            for (w_s, w_e) in wins:
                w_end = w_e if w_e != time(0,0) else time(23,59)
                inside = [dm for dm in day_dems
                          if (e.id, dm.id) in X
                          and dm.start >= w_s
                          and (dm.end if dm.end != time(0,0) else time(23,59)) <= w_end]
                if inside:
                    mdl.Add(sum(X[e.id, dm.id] for dm in inside) >= 1)

def add_anchor_must_cover_two_starts(mdl, emps, dem, X, overrides: Set[Tuple[str, date]]):
    """
    Para días con dos starts (us_two_starts_dow) y NO override:
    Si existe demanda cuyo start == inicio exacto de la ventana US, obliga a cubrir al menos
    un segmento que arranque ahí (por cada ventana del día).
    """
    from collections import defaultdict
    by_day = defaultdict(list)
    for dm in dem:
        by_day[dm.date].append(dm)

    def tend(t: time) -> time:
        return t if t != time(0,0) else time(23,59)

    for e in emps:
        for day, dlist in by_day.items():
            if (e.id, day) in overrides:
                continue  # solo en US enforzado
            dow = day.weekday()
            if dow not in getattr(e, "us_two_starts_dow", set()):
                continue

            wins = sorted(e.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1])))
            if not wins:
                continue

            for (w_s, w_e) in wins:
                w_end = tend(w_e)
                # candidatos: start EXACTO en w_s y dentro de esa ventana
                cands = []
                for dm in dlist:
                    if (e.id, dm.id) not in X:
                        continue
                    if not e.can(dm.wsid):
                        continue
                    end = tend(dm.end)
                    if dm.start == w_s and end <= w_end:
                        cands.append(dm)
                # Si existe al menos uno, exijo cubrirlo
                if cands:
                    mdl.Add(sum(X[e.id, dm.id] for dm in cands) >= 1)
                    if ASCII_LOGS:
                        hhmm = w_s.strftime("%H:%M")
                        print(f"[ANCHOR-HARD-2STARTS] {e.name} {day} → debe cubrir inicio US {hhmm}")


# ───────── Utilidades solver (estricto/flexible) ─────────
def groups_without_usershift_candidates(
    emps: List[Emp],
    dem: List[Demand],
    overrides_emp_day: Set[Tuple[str, date]]
):
    """
    Marca (fecha, wsid) que deben relajarse SÓLO si no hay ningún candidato:
      - En override (free_mode) → cuenta como candidato directo.
      - Con UserShift ese día y cuya ventana contenga la demanda (IGNORANDO shift_type).
      - Sin UserShift ese día pero disponible().

    IMPORTANTE: aquí NO filtramos por shift_type; así evitamos relajar el grupo
    cuando sí existen ventanas US viables temporalmente.
    """
    group_needs_relax = set()
    by_group = defaultdict(list)
    for d in dem:
        by_group[(d.date, d.wsid)].append(d)

    for (gdate, wsid), dlist in sorted(by_group.items(), key=lambda x: (x[0][0], str(x[0][1]))):
        found_any = False
        dow = gdate.weekday()

        for emp in emps:
            # Si alguno de los dm del grupo no es del rol del empleado, seguiremos evaluando cada dm.
            # 1) Si el día está en override, damos por bueno (modo libre).
            if (emp.id, gdate) in overrides_emp_day:
                found_any = True
                break

            wins = emp.user_shift_windows.get(dow, [])
            if wins:
                # 2) Con UserShift: basta que ALGUNA demanda del grupo caiga dentro de ALGUNA ventana
                #    (ignoramos shift_type aquí a propósito).
                for dm in dlist:
                    if not emp.can(dm.wsid):
                        continue
                    dm_end = dm.end if dm.end != time(0, 0) else time(23, 59)
                    if any(dm.start >= w_s and dm_end <= (w_e if w_e != time(0, 0) else time(23, 59))
                           for (w_s, w_e) in wins):
                        found_any = True
                        break
                if found_any:
                    break
            else:
                # 3) Sin UserShift: basta disponibilidad general.
                for dm in dlist:
                    if not emp.can(dm.wsid):
                        continue
                    if emp.available(dm.date, dm.start, dm.end):
                        found_any = True
                        break
                if found_any:
                    break

        if not found_any:
            group_needs_relax.add((gdate, wsid))
            if ASCII_LOGS:
                print(f"[RELAX-GRUPO] (fecha={gdate}, wsid={wsid})")

    return group_needs_relax


def add_no_gaps_inside_usershift_windows(mdl, emps, dem, X):
    """Prohíbe patrón 1-0-1 dentro de una MISMA ventana de UserShift."""
    from collections import defaultdict
    by_day = defaultdict(list)
    for dm in dem:
        by_day[dm.date].append(dm)

    def tend(t: time) -> time:
        return t if t != time(0,0) else time(23,59)

    def tmin(t: time) -> int:
        t = tend(t)
        return t.hour*60 + t.minute

    for e in emps:
        for day, dlist in by_day.items():
            dow = day.weekday()
            wins = e.user_shift_windows.get(dow, [])
            if not wins:
                continue
            for (ws, we) in wins:
                inside = [dm for dm in dlist
                          if (e.id, dm.id) in X
                          and dm.start >= ws
                          and tend(dm.end) <= tend(we)]
                inside.sort(key=lambda z: (tmin(z.start), tmin(z.end)))
                for i in range(1, len(inside)-1):
                    a, b, c = inside[i-1], inside[i], inside[i+1]
                    mdl.Add(X[e.id, b.id] >= X[e.id, a.id] + X[e.id, c.id] - 1)

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

def add_min_gap_between_blocks_any_free_mode(mdl, emps, dem, X, overrides: set[tuple[str, date]], min_gap_hours: int):
    if not min_gap_hours or min_gap_hours <= 0: return
    min_gap_min = min_gap_hours * 60
    by_day = defaultdict(list)
    for d in dem: by_day[d.date].append(d)

    def t_end(t: time) -> time: return t if t != time(0,0) else time(23,59)

    for e in emps:
        for day, lst in by_day.items():
            if (e.id, day) not in overrides:  # solo libre
                continue
            lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(t_end(z.end))))
            n = len(lst)
            for i in range(n):
                a = lst[i]; a_end_m = _t2m(t_end(a.end))
                for j in range(i+1, n):
                    b = lst[j]
                    if not (a.end <= b.start):  # solapados o contiguos = mismo bloque
                        continue
                    gap = _t2m(b.start) - a_end_m
                    if 0 < gap < min_gap_min and (e.id, a.id) in X and (e.id, b.id) in X:
                        mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

def add_min_per_contiguous_block_free_mode(mdl, emps, dem, X,
                                           overrides: set[tuple[str, date]],
                                           min_hours: int):
    """
    En ASIGNACIÓN LIBRE (override):
      - Se permiten microturnos consecutivos (cualquier puesto) que formen BLOQUES contiguos.
      - Cada BLOQUE activo debe durar al menos 'min_hours' (3h).
      - La contigüidad es global por DÍA (no por puesto): start_{k+1} == end_k (minutos).
    """
    if not min_hours or min_hours <= 0:
        return
    min_min = int(min_hours * 60)

    # Agrupar solo por DÍA
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    def tend(t: time) -> time:
        return t if t != time(0,0) else time(23,59)

    for e in emps:
        for day, lst in by_day.items():
            if (e.id, day) not in overrides:
                continue  # solo libre
            # Orden global por día
            lst = sorted(lst, key=lambda z: (_t2m(z.start), _t2m(tend(z.end))))
            n = len(lst)
            i = 0
            while i < n:
                j = i
                cur_end = _t2m(tend(lst[i].end))
                minutes_terms, used_vars = [], []
                if (e.id, lst[i].id) in X:
                    minutes_terms.append(duration_min(lst[i]) * X[e.id, lst[i].id])
                    used_vars.append(X[e.id, lst[i].id])

                # encadenar CONTIGUOS exactos por día (da igual el puesto)
                while j + 1 < n and _t2m(lst[j+1].start) == cur_end:
                    j += 1
                    cur_end = _t2m(tend(lst[j].end))
                    if (e.id, lst[j].id) in X:
                        minutes_terms.append(duration_min(lst[j]) * X[e.id, lst[j].id])
                        used_vars.append(X[e.id, lst[j].id])

                if used_vars:
                    y_blk = mdl.NewBoolVar(f"blk_free_GLOBAL_{e.id}_{day.isoformat()}_{i}_{j}")
                    mdl.Add(sum(used_vars) >= y_blk)
                    mdl.Add(sum(used_vars) <= 1000 * y_blk)
                    mdl.Add(sum(minutes_terms) >= min_min * y_blk)
                i = j + 1


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

def build_usershift_anchor_start_preference(mdl, emps, dem, X, overrides: set[tuple[str, date]]):
    """
    Preferencia suave: si el día NO está en override y existe 'ancla' (primer inicio)
    para (empleado, día), intenta que ese empleado cubra ALGÚN segmento cuyo start sea
    exactamente ese primer inicio detectado.
    Además, imprime logs para explicar CUANDO es posible anclar y POR QUÉ no lo es.
    """
    
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    def _why_no_X_for_anchor(e, dm, free_today: bool) -> str | None:
        """
        Replica la lógica de creación de variables (versión flexible) para explicar
        por qué NO hay X en el segmento ancla. Devuelve None si 'sí podría' crear X.
        """
        dow = dm.date.weekday()
        end = dm.end if dm.end != time(0,0) else time(23,59)

        if not e.can(dm.wsid):
            return "rol_no_habilitado"

        # Si hay US enforzado (no override), el segmento debe caer dentro de US
        if e.user_shift_windows.get(dow) and not free_today:
            in_us = any(dm.start >= ws and end <= (we if we != time(0,0) else time(23,59))
                        for (ws, we) in sorted(e.user_shift_windows[dow], key=lambda w: (_t2m(w[0]), _t2m(w[1]))))
            if not in_us:
                return "fuera_de_ventana_usershift"

        else:
            # Sin US enforzado: si hay ST ese día, debe caer en ventana ST
            st_wins = e.shift_type_windows.get(dow, [])
            
            if st_wins:
                in_st = any(dm.start >= ws and end <= we for (ws, we) in st_wins)
                if not in_st:
                    return "fuera_de_ventana_shifttype"
            # En override (free) respetamos disponibilidad general
            if free_today and not e.available(dm.date, dm.start, dm.end):
                return "fuera_de_disponibilidad_general"

        # Si llega aquí, SÍ podríamos crear X
        return None

    terms = []
    for e in emps:
        anchors = getattr(e, 'user_shift_anchor_by_date', {})
        for day, day_dems in sorted(by_day.items(), key=lambda kv: kv[0]):
            free_today = (e.id, day) in overrides

            # Si es override, no empujamos ancla (pero logeamos por qué se omite)
            if free_today:
                if ASCII_LOGS:
                    print(f"[ANCHOR] {e.name} {day} → omitido (override/free_mode).")
                continue

            anchor_t = anchors.get(day)
            if not anchor_t:
                if ASCII_LOGS:
                    print(f"[ANCHOR] {e.name} {day} → sin ancla (no había segmento dentro de US).")
                continue

            anchor_min = _t2m(anchor_t)
            # Todos los segmentos del día que empiezan EXACTO en el ancla (independiente de X)
            anchored_segments = [dm for dm in day_dems if _t2m(dm.start) == anchor_min]

            # De esos, ¿cuáles tienen X creada?
            earliest_set = [dm for dm in anchored_segments if (e.id, dm.id) in X]

            if earliest_set:
                if ASCII_LOGS:
                    ws_list = ", ".join(f"{dm.wsname}" for dm in earliest_set[:5])
                    print(f"[ANCHOR] {e.name} {day} → ancla {anchor_t.strftime('%H:%M')} "
                          f"VIABLE: {len(earliest_set)} opciones (ej: {ws_list}).")
                y = mdl.NewBoolVar(f"y_anchor_{e.id}_{day.isoformat()}")
                mdl.Add(sum(X[e.id, dm.id] for dm in earliest_set) >= y)
                mdl.Add(sum(X[e.id, dm.id] for dm in earliest_set) <= 1000 * y)
                terms.append(1 - y)
            else:
                # No hay X en la ancla: busca la PRIMERA razón y logéala
                reason = "sin_variables_X"  # fallback
                for dm in anchored_segments:
                    r = _why_no_X_for_anchor(e, dm, free_today)
                    if r:
                        reason = r
                        break
                if ASCII_LOGS:
                    print(f"[ANCHOR] {e.name} {day} → ancla {anchor_t.strftime('%H:%M')} "
                          f"NO viable ({reason}).")
    return sum(terms) if terms else 0



def build_usershift_window_penalty(mdl, emps, dem, X, overrides=set()):
    penalties = []
    for d in dem:
        dow = d.date.weekday()
        for e in emps:
            key = (e.id, d.id)
            if key not in X:
                continue

            # ¿Hay US hoy?
            has_us = bool(e.user_shift_windows.get(dow, []))
            if not has_us:
                continue

            end = d.end if d.end != time(0,0) else time(23,59)
            in_any = any(d.start >= ws and end <= (we if we != time(0,0) else time(23,59))
                         for (ws, we) in e.user_shift_windows.get(dow, []))

            # Regla original: con US enforzado (no override) se penaliza si sale
            us_enforced = has_us and ((e.id, d.date) not in overrides)

            # --- NUEVO: si ese DOW tiene DOS starts, penalizamos fuera de US SIEMPRE ---
            two_starts_today = (dow in getattr(e, "us_two_starts_dow", set()))
            penalize_today = us_enforced or two_starts_today

            if penalize_today and not in_any:
                z = mdl.NewBoolVar(f"pen_outside_us_{e.id}_{d.id}")
                mdl.Add(z >= X[key])
                penalties.append(z)

                if ASCII_LOGS and two_starts_today:
                    print(f"[US-PENALTY-2STARTS] {e.name} {d.date.isoformat()} fuera de US → penalizado (dos Block1Start)")

    return (WEIGHT_USERWINDOW * sum(penalties)) if penalties else 0

def build_free_mode_balance_penalty(mdl, emps, dem, X, overrides: Set[Tuple[str, date]]):
    """
    Penaliza la desigualdad de minutos asignados en modo libre (overrides).
    Minimizamos sum |W_e - M|, donde W_e = minutos libres asignados al empleado e,
    y M es un “centro” que el modelo elige. SOLO cuenta días en override.
    """
    # Upper bound conservador: minutos totales demandados
    UB = 0
    for dm in dem:
        end = dm.end if dm.end != time(0, 0) else time(23, 59)
        mins = (end.hour * 60 + end.minute) - (dm.start.hour * 60 + dm.start.minute)
        if mins > 0:
            UB += mins * dm.need
    UB = max(UB, 24 * 60)

    # Empleados que tienen al menos un día en libre
    emps_with_free = []
    dates = sorted({d.date for d in dem})
    has_override_day = {e.id: any((e.id, day) in overrides for day in dates) for e in emps}
    for e in emps:
        if has_override_day.get(e.id, False):
            emps_with_free.append(e)
    if not emps_with_free:
        return 0

    # W_e = minutos asignados en días libres
    W = {}
    for e in emps_with_free:
        expr_terms = []
        for dm in dem:
            key = (e.id, dm.id)
            if key in X and (e.id, dm.date) in overrides:
                end = dm.end if dm.end != time(0, 0) else time(23, 59)
                mins = (end.hour * 60 + end.minute) - (dm.start.hour * 60 + dm.start.minute)
                if mins > 0:
                    expr_terms.append(mins * X[key])
        wi = mdl.NewIntVar(0, UB, f"free_min_{e.id}")
        if expr_terms:
            mdl.Add(wi == sum(expr_terms))
        else:
            mdl.Add(wi == 0)
        W[e.id] = wi

    # Centro común
    M = mdl.NewIntVar(0, UB, "free_min_center")

    # Desviaciones absolutas |W_e - M|
    deviations = []
    for e in emps_with_free:
        te = mdl.NewIntVar(0, UB, f"free_dev_{e.id}")
        mdl.Add(te >= W[e.id] - M)
        mdl.Add(te >= M - W[e.id])
        deviations.append(te)

    return sum(deviations)



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



def add_min_per_contiguous_block_enforced(mdl, emps, dem, X, min_hours: int, overrides: set[tuple[str, date]]):
    """Como add_min_per_contiguous_block, pero solo obliga el mínimo por bloque
    cuando el día NO está en override (asignación libre). En override permite bloques < min_hours."""
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
            if (e.id, day) in overrides:
                continue  # en días libres no exigimos bloque mínimo por puesto
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
                    y_blk = mdl.NewBoolVar(f"blk_enf_{e.id}_{day.isoformat()}_{wsid}_{i}_{j}")
                    mdl.Add(sum(used_vars) >= y_blk)
                    mdl.Add(sum(used_vars) <= 1000 * y_blk)
                    mdl.Add(sum(minutes_terms) >= min_min * y_blk)
                i = j + 1


def add_daily_min_minutes_for_override(mdl, emps, dem, X, min_hours: int, overrides: set[tuple[str, date]]):
    """En días override: si el empleado trabaja algo ese día, total >= min_hours."""
    if not min_hours or min_hours <= 0:
        return
    min_min = int(min_hours * 60)

    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    for e in emps:
        for day, lst in by_day.items():
            if (e.id, day) not in overrides:
                continue
            todays = [(e.id, dm.id) for dm in lst if (e.id, dm.id) in X]
            if not todays:
                continue
            y = mdl.NewBoolVar(f"y_override_{e.id}_{day.isoformat()}")
            mdl.Add(sum(X[k] for k in todays) >= y)
            mdl.Add(sum(X[k] for k in todays) <= 1000 * y)
            total_min = sum(duration_min(dm) * X[e.id, dm.id] for dm in lst if (e.id, dm.id) in X)
            mdl.Add(total_min >= min_min * y)

def build_free_mode_balance_days_penalty(mdl, emps, dem, X, overrides_emp_day):
    """
    Devuelve el 'spread' (max - min) de DÍAS trabajados por persona en días override.
    Mientras más grande, peor repartido está el número de días.
    """
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    work_days = {}  # eid -> suma de días (BoolVars)
    for e in emps:
        terms = []
        for day, lst in by_day.items():
            if (e.id, day) not in overrides_emp_day:
                continue  # sólo contamos días en modo libre
            todays = [(e.id, dm.id) for dm in lst if (e.id, dm.id) in X]
            if not todays:
                continue
            y = mdl.NewBoolVar(f"y_free_day_{e.id}_{day.isoformat()}")
            mdl.Add(sum(X[k] for k in todays) >= y)
            mdl.Add(sum(X[k] for k in todays) <= 1000 * y)
            terms.append(y)
        work_days[e.id] = sum(terms) if terms else 0

    if not work_days:
        return 0

    Dmax = mdl.NewIntVar(0, 7, "free_days_max")
    Dmin = mdl.NewIntVar(0, 7, "free_days_min")
    for eid, De in work_days.items():
        mdl.Add(De <= Dmax)
        mdl.Add(De >= Dmin)

    spread = mdl.NewIntVar(0, 7, "free_days_spread")
    mdl.Add(spread == Dmax - Dmin)
    return spread


def add_max_two_days_off_soft(mdl, emps, dem, X,
                              business_days: set[int] = BUSINESS_DAYS,
                              max_off: int = MAX_BUSINESS_DAYS_OFF):
    """
    Regla suave: en días de negocio (p.ej. Lun–Sáb), cada empleado debe trabajar al menos
    (#días factibles - max_off). Si no llega, se penaliza con una variable 'short' (no infactible).
    Devuelve: (penalty_expr, meta) donde 'meta' sirve para construir diagnósticos post-solve.
    """
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    biz_dates = sorted({d.date for d in dem if d.date.weekday() in business_days})
    y_work = {}       # (eid, day) -> BoolVar (trabajó ese día)
    can_work = {}     # (eid, day) -> bool (existen variables X ese día)
    candidates = {}   # (eid, day) -> [dm.id] candidatas
    short_vars = {}   # eid -> IntVar de déficit
    penalty_terms = []

    for e in emps:
        y_days = []
        for day in biz_dates:
            todays = [dm for dm in by_day.get(day, []) if (e.id, dm.id) in X]
            can = bool(todays)
            can_work[(e.id, day)] = can
            candidates[(e.id, day)] = [dm.id for dm in todays]
            if not todays:
                continue
            y = mdl.NewBoolVar(f"y_work_{e.id}_{day.isoformat()}")
            mdl.Add(sum(X[e.id, dm.id] for dm in todays) >= y)
            mdl.Add(sum(X[e.id, dm.id] for dm in todays) <= 1000 * y)
            y_work[(e.id, day)] = y
            y_days.append(y)

        if y_days:
            required = max(0, len(y_days) - max_off)
            short = mdl.NewIntVar(0, len(y_days), f"short_days_{e.id}")
            # sum(y_days) + short >= required  → short absorbe el déficit
            mdl.Add(sum(y_days) + short >= required)
            short_vars[e.id] = short
            penalty_terms.append(short)

    penalty_expr = sum(penalty_terms) if penalty_terms else 0
    meta = {
        "y_work": y_work,
        "can_work": can_work,
        "candidates": candidates,
        "short": short_vars,
        "biz_dates": biz_dates,
    }
    return penalty_expr, meta


def add_hard_max_business_days_off(mdl, emps, dem, X, week, max_off=2):
    business_days = {0,1,2,3,4,5}
    from collections import defaultdict
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)

    bus_days = [d for d in sorted({dm.date for dm in dem}) if d.weekday() in business_days]
    for e in emps:
        y_flags = []
        for day in bus_days:
            todays = [dm for dm in by_day.get(day, []) if (e.id, dm.id) in X]
            if not todays:
                continue
            y = mdl.NewBoolVar(f"y_work_bus_{e.id}_{day.isoformat()}")
            mdl.Add(sum(X[e.id, dm.id] for dm in todays) >= y)
            mdl.Add(sum(X[e.id, dm.id] for dm in todays) <= 1000 * y)
            y_flags.append(y)
        if y_flags:
            mdl.Add(sum(y_flags) >= max(0, len(y_flags) - max_off))


def build_days_off_diagnostics(solver, meta, emps, dem):
    """
    Construye diagnóstico legible tras resolver: quién no cumplió, qué días y por qué.
    'por qué':
      - "sin demandas compatibles (roles/ventanas/ausencias)" si no hubo variables X ese día.
      - "sin asignación (priorización/penalizaciones)" si hubo candidatas pero no se asignó.
    """
    dem_by_id = {d.id: d for d in dem}
    name_by_emp = {e.id: e.name for e in emps}
    out = []

    for eid, short in meta["short"].items():
        missing = int(solver.Value(short))
        if missing <= 0:
            continue

        eligible_days = [day for day in meta["biz_dates"] if (eid, day) in meta["y_work"]]
        worked_count = sum(int(bool(solver.Value(meta["y_work"][(eid, day)]))) for day in eligible_days)
        required_min = max(0, len(eligible_days) - MAX_BUSINESS_DAYS_OFF)

        details = []
        for day in eligible_days:
            did = bool(solver.Value(meta["y_work"][(eid, day)]))
            if did:
                continue
            cand_dm_ids = meta["candidates"].get((eid, day), [])
            puestos = sorted({dem_by_id[x].wsname for x in cand_dm_ids if x in dem_by_id})
            motivo = ("sin demandas compatibles (roles/ventanas/ausencias)" if not cand_dm_ids
                      else "sin asignación (priorización/penalizaciones)")
            details.append({
                "date": day.isoformat(),
                "puestos_candidatos": puestos,
                "motivo": motivo
            })

        out.append({
            "employee_id": str(eid),
            "employee_name": name_by_emp.get(eid, ""),
            "eligible_days": len(eligible_days),
            "required_min": required_min,
            "worked_days": worked_count,
            "missing_days": missing,
            "detail": details
        })
    return out

def build_variables(mdl, emps, dem, overrides_emp_day, relax_groups):
    X = {}
    dem_sorted = sorted(dem, key=lambda d: (d.date, _t2m(d.start), _t2m(d.end), str(d.wsid)))
    for d in dem_sorted:
        for e in emps:
            # 🚫 Día libre (RT0) o AUSENTE → no crear variable
            if e.off(d.date) or e.absent_day(d.date):
                if ASCII_LOGS:
                    print(f"[VARS/SKIP-ABS] {e.name} {d.date} → libre/ausente; no candidato.")
                continue

            # Prioridad CA1: si el día NO está en overrides (usershift_enforced),
            # no aplicamos disponibilidad general; sólo verificamos habilitación.
            free_today = (e.id, d.date) in overrides_emp_day
            if not e.can(d.wsid): 
                continue
            if free_today and not e.available(d.date, d.start, d.end):
                # en free_mode sí respetamos disponibilidad general
                continue
            # si el grupo está relajado, permitimos fuera de ventana de usershift

            relax_this_group = (d.date, d.wsid) in relax_groups
            dow = d.date.weekday()
            end = d.end if d.end != time(0,0) else time(23,59)
            free_today = (e.id, d.date) in overrides_emp_day

            # si el empleado tiene ventana ese día y NO está en override/relax
            if not free_today and not relax_this_group and e.user_shift_windows.get(dow):
                in_window = False
                # ordenar por inicio
                for w_s, w_e in sorted(e.user_shift_windows[dow], key=lambda w: (_t2m(w[0]), _t2m(w[1]))):
                    w_end = w_e if w_e != time(0, 0) else time(23, 59)
                    if d.start >= w_s and end <= w_end:
                        in_window = True
                        break
                if not in_window:
                    continue  # ← fuera de ventana US; no crear variable para este emp-dem

            # [PATCH] No exigimos compatibilidad de shift_type en usershift_enforced
            X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")

            if ASCII_LOGS:
                print(f"[VARS]  {{'comb': {len(emps)*len(dem)}, 'allow': {len(X)}}}")

    return X


def build_variables_with_usershift_logic(mdl, emps, dem, overrides: Set[Tuple[str, date]]):
    X = {}
    dem_sorted = sorted(dem, key=lambda d: (d.date, _t2m(d.start), _t2m(d.end), str(d.wsid)))

    for d in dem_sorted:
        dow = d.date.weekday()

        def prio(e):
            us_enf = (e.user_shift_windows.get(dow) and (e.id, d.date) not in overrides)
            st_day = bool(e.shift_type_windows.get(dow))
            return (0 if us_enf else (1 if st_day else 2), len(e.roles), e.name)

        for e in sorted(emps, key=prio):
            # 🚫 Día libre (RT0) o AUSENTE → fuera
            if e.off(d.date) or e.absent_day(d.date):
                if ASCII_LOGS:
                    print(f"[VARS2/SKIP-ABS] {e.name} {d.date} → libre/ausente; no candidato.")
                continue

            if not e.can(d.wsid):
                continue

            free_today = (e.id, d.date) in overrides
            two_starts_today = (dow in getattr(e, "us_two_starts_dow", set()))  # ← FIX NameError

            # US enforzado: debe caer dentro de alguna ventana US (no exigimos ST)
            if e.user_shift_windows.get(dow) and not free_today:
                end = d.end if d.end != time(0,0) else time(23,59)
                in_us = any(d.start >= ws and end <= (we if we != time(0,0) else time(23,59))
                            for ws, we in sorted(e.user_shift_windows[dow], key=lambda w: (_t2m(w[0]), _t2m(w[1]))))
                if not in_us:
                    continue

            else:
                # Sin US enforzado: primero intentamos con ShiftTypes
                st_wins = e.shift_type_windows.get(dow, [])
                end_seg = d.end if d.end != time(0,0) else time(23,59)
                in_st = any(d.start >= ws and end_seg <= we for (ws, we) in st_wins) if st_wins else False

                if not in_st:
                    # BYPASS en día con dos starts: si cae dentro de alguna ventana US, lo aceptamos
                    us_wins = e.user_shift_windows.get(dow, [])
                    in_us = any(d.start >= ws and end_seg <= (we if we != time(0,0) else time(23,59))
                                for (ws, we) in us_wins) if us_wins else False
                    flex_day = getattr(e, "usershift_flex_days", {}).get(dow, False)

                    if not (flex_day or (two_starts_today and in_us)):
                        continue

                # En override respetamos disponibilidad general
                if free_today and not e.available(d.date, d.start, d.end):
                    continue

                if ASCII_LOGS and two_starts_today and st_wins:
                    print(f"[ST-BYPASS-2STARTS] {e.name} {d.date.isoformat()} DOW={dow} → "
                          f"permitimos dentro de US aunque no haya ventana ST")

            X[e.id, d.id] = mdl.NewBoolVar(f"x_{e.id}_{d.id}")

    if ASCII_LOGS:
        print(f"[VARS] Variables creadas: {len(X)} de {len(emps)*len(dem)} posibles")
    return X


# ───────── SOLVER ESTRICTO ─────────
def solve(emps: List[Emp], dem: List[Demand], week: List[date],
          overrides_emp_day: Set[Tuple[str, date]], min_hours_required: int = 0):
    relax_groups = groups_without_usershift_candidates(emps, dem, overrides_emp_day)
    mdl = cp_model.CpModel()
    X = build_variables(mdl, emps, dem, overrides_emp_day, relax_groups)
    if not X:
        raise ScheduleGenerationError("Sin variables: reglas dejan todo vacío.")

    # Cobertura exacta de cada segmento
    for d in dem:
        mdl.Add(sum(X[e.id, d.id] for e in emps if (e.id, d.id) in X) == d.need)

    # No solapes por empleado/día
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)
    for day in sorted(by_day.keys()):
        lst = sorted(by_day[day], key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i + 1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # Máx. 9h/día por empleado
    for e in emps:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                mdl.Add(sum(duration_min(dm) * X[e.id, dm.id] for dm in todays) <= MAX_HOURS_PER_DAY * 60)
    add_max_days_worked_per_week(mdl, emps, dem, X, week, max_days=MAX_DAYS_PER_WEEK)


    # (Opcional) mín. horas/semana legales
    if min_hours_required > 0:
        for e in emps:
            week_assignments = [dm for dm in dem if (e.id, dm.id) in X]
            if week_assignments:
                total_minutes_week = sum(duration_min(dm) * X[e.id, dm.id] for dm in week_assignments)
                mdl.Add(total_minutes_week >= min_hours_required * 60)

    # Descanso mínimo entre cierre y apertura (día siguiente)
    for e in emps:
        for a in dem:
            for b in dem:
                if b.date == a.date + timedelta(days=1) and (e.id, a.id) in X and (e.id, b.id) in X:
                    if (24*60 - to_min(a.end)) + to_min(b.start) < MIN_HOURS_BETWEEN_SHIFTS * 60:
                        mdl.Add(X[e.id, a.id] + X[e.id, b.id] <= 1)

    # Reglas de bloques y libre
    add_max2_blocks_per_day(mdl, emps, dem, X)
    add_min_gap_between_blocks_any_free_mode(mdl, emps, dem, X, overrides_emp_day, MIN_HOURS_BETWEEN_SPLIT)  # gap ≥ 3h en libre
    add_min_per_contiguous_block_free_mode(mdl, emps, dem, X, overrides_emp_day, MIN_SHIFT_DURATION_HOURS)   # global en libre
    # Gap mínimo entre ventanas del mismo día (si hay 2 US)
    add_min_split_gap_usershift_windows(mdl, emps, dem, X, MIN_HOURS_BETWEEN_SPLIT)

    # Bloque mínimo ≥ MIN_SHIFT_DURATION_HOURS cuando NO es override
    add_min_per_contiguous_block_global_enforced(mdl, emps, dem, X, overrides_emp_day, MIN_SHIFT_DURATION_HOURS)

    
    add_no_gaps_inside_usershift_windows(mdl, emps, dem, X)
    add_hard_max_business_days_off(mdl, emps, dem, X, week, max_off=MAX_BUSINESS_DAYS_OFF)
    # En días override: si trabaja algo, total día ≥ MIN_SHIFT_DURATION_HOURS
    add_daily_min_minutes_for_override(mdl, emps, dem, X, MIN_SHIFT_DURATION_HOURS, overrides_emp_day)


    # Obligación de cubrir UserShift al inicio de ventana (si aplica)
    add_usershift_must_cover_if_possible_with_overrides(mdl, emps, dem, X, overrides_emp_day)

    # Objetivo (must-have-one por grupo + consolidación + penalización fuera de ventana US)
    groups = defaultdict(list)
    for d in dem:
        groups[(d.date, d.wsid)].append(d)
    group_penalties = []
    for gk, dlist in sorted(groups.items(), key=lambda g: (g[0][0], str(g[0][1]))):
        gvar = mdl.NewBoolVar(f"grp_cover_{gk[0].isoformat()}_{gk[1]}")
        for d in dlist:
            for e in emps:
                if (e.id, d.id) in X:
                    mdl.AddImplication(X[e.id, d.id], gvar)
        group_penalties.append(1 - gvar)

    consolidation_cost = build_consolidation_cost(mdl, emps, dem, X)
    
    usershift_penalty  = build_usershift_window_penalty(mdl, emps, dem, X, overrides_emp_day)
    penalty_days_off, meta_days_off = add_max_two_days_off_soft(mdl, emps, dem, X)
    fair_free_penalty = build_free_mode_balance_penalty(mdl, emps, dem, X, overrides_emp_day)
    anchor_pref_penalty = build_usershift_anchor_start_preference(mdl, emps, dem, X, overrides_emp_day)

    # Penalización por usar roles de fallback (preferir rol titular si es posible)
    role_downgrade_terms = []
    for d in dem:
        for e in emps:
            if (e.id, d.id) in X and hasattr(e, "roles_originales") and d.wsid not in e.roles_originales:
                role_downgrade_terms.append(X[e.id, d.id])
    role_downgrade_penalty = WEIGHT_ROLE_DOWNGRADE * (sum(role_downgrade_terms) if role_downgrade_terms else 0)
    

    mdl.Minimize(
        sum(group_penalties) * WEIGHT_MUST_HAVE_ONE
        + WEIGHT_CONSOLIDATE * consolidation_cost
        + usershift_penalty
        + WEIGHT_DAYS_OFF * penalty_days_off
        + WEIGHT_FAIR_FREE * fair_free_penalty
        + WEIGHT_US_ANCHOR_START * anchor_pref_penalty
        + role_downgrade_penalty
    )

    # Resolver
    sol = cp_model.CpSolver()
    sol.parameters.random_seed = 0
    sol.parameters.num_search_workers = 1
    sol.parameters.max_time_in_seconds = 120
    st = sol.Solve(mdl)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ScheduleGenerationError("Modelo sin solución")

    # Extraer solución
    out = defaultdict(list)
    for d in dem:
        for e in emps:
            if (e.id, d.id) in X and sol.Value(X[e.id, d.id]):
                out[d.date].append((e, d))
    days_off_diag = build_days_off_diagnostics(sol, meta_days_off, emps, dem)
    return out, relax_groups, days_off_diag


# ───────── SOLVER FLEXIBLE ─────────
# ───────── SOLVER FLEXIBLE ─────────
def solve_flexible(
    emps: List[Emp],
    dem: List[Demand],
    week: List[date],
    overrides: Set[Tuple[str, date]],
    min_hours_required: int = 0
):
    """Solver en dos fases; nunca infactible. Devuelve (schedule, coverage_stats, days_off_diag)."""
    usershift_emps, other_emps = [], []
    for e in emps:
        has_usershift_any_day = any(
            e.user_shift_windows.get(d.weekday()) and (e.id, d) not in overrides
            for d in week
        )
        (usershift_emps if has_usershift_any_day else other_emps).append(e)

    if ASCII_LOGS:
        print(f"[SOLVER] Fase 1 (UserShift): {len(usershift_emps)} empleados")
        print(f"[SOLVER] Fase 2 (complemento): {len(other_emps)} empleados")

    try:
        # ----- Fase CP-SAT -----
        sched_p1, cov_p1, remaining, diag1 = _solve_with_employees(
            usershift_emps if usershift_emps else emps,
            dem,
            week,
            overrides,
            min_hours_required,
        )

        if remaining:
            if ASCII_LOGS:
                print(f"[SOLVER] Fase 2: {len(remaining)} demandas restantes")
            sched_p2, cov_p2, _, diag2 = _solve_with_employees(
                emps,
                remaining,
                week,
                overrides,
                min_hours_required,
            )

            # Combinar fase 1 + fase 2
            final_sched = defaultdict(list)
            for day, assigns in sched_p1.items():
                final_sched[day].extend(assigns)
            for day, assigns in sched_p2.items():
                final_sched[day].extend(assigns)

            final_cov = {**cov_p1, **cov_p2}
            final_diag = (diag1 or []) + (diag2 or [])
            return final_sched, final_cov, final_diag
        else:
            return sched_p1, cov_p1, (diag1 or [])

    except ScheduleGenerationError as e:
        # ----- Fallback GREEDY -----
        if ASCII_LOGS:
            print(f"[SOLVER] Fallback GREEDY por error en CP-SAT: {e}")
        sched, coverage_stats = greedy_fallback(emps, dem, week, overrides)
        # greedy no calcula days_off_diag
        return sched, coverage_stats, []

def _solve_with_employees(emps_subset: List[Emp],dem: List[Demand],week: List[date],overrides: Set[Tuple[str, date]],min_hours_required: int = 0):
    """Resuelve con un subconjunto de empleados. Devuelve (schedule, coverage_stats, remaining_demands, days_off_diag)."""
    mdl = cp_model.CpModel()
    X = build_variables_with_usershift_logic(mdl, emps_subset, dem, overrides)
    if ASCII_LOGS:
        print("\n=== DEBUG CANDIDATOS JUEVES ≥ 20:00 (PARRILLA/ENLACE) ===")
        for dseg in dem:
            if dseg.date.weekday() != 3:  # 3 = jueves
                continue
            if dseg.start < time(20,0):
                continue
            if dseg.wsname.upper() not in {"PARRILLA","PARRILLERO","APOYO ENLACE"}:
                continue
            rest = [e.name for e in emps_subset if (e.id, dseg.id) in X and ((e.id, dseg.date) not in overrides)]
            free = [e.name for e in emps_subset if (e.id, dseg.id) in X and ((e.id, dseg.date) in overrides)]
            print(f"{dseg.wsname} {dseg.start}-{dseg.end} need={dseg.need}  |  restringidos={rest}  libres={free}")

    if not X:
        raise ScheduleGenerationError("Sin variables viables")

    # unmet por segmento (permitimos uncovered con penalización)
    unmet = {d.id: mdl.NewIntVar(0, d.need, f"unmet_{d.id}") for d in dem}
    for d in dem:
        covered = sum(X[e.id, d.id] for e in emps_subset if (e.id, d.id) in X)
        mdl.Add(covered + unmet[d.id] == d.need)
        # ── RESTRICCIÓN (con slack) para priorizar RESTRINGIDOS sobre LIBRES en cada segmento ──
    # Si hay R candidatos restringidos para el segmento, pedimos usar hasta min(need, R).
    # Si el modelo usa menos restringidos de los posibles, aparece un slack penalizado en el objetivo.
    restricted_shortfall_terms = []
    for dseg in dem:
        R_vars = [X[e.id, dseg.id] for e in emps_subset
                  if (e.id, dseg.id) in X and ((e.id, dseg.date) not in overrides)]
        F_vars = [X[e.id, dseg.id] for e in emps_subset
                  if (e.id, dseg.id) in X and ((e.id, dseg.date) in overrides)]
        if not R_vars or not F_vars:
            continue  # si no hay mezcla R/F, no hace falta esta pieza

        min_req_restricted = min(dseg.need, len(R_vars))
        slack = mdl.NewIntVar(0, min_req_restricted, f"short_restricted_{dseg.id}")
        # Usar 'slack' sólo si no alcanzamos min_req_restricted con restringidos
        mdl.Add(sum(R_vars) + slack >= min_req_restricted)
        restricted_shortfall_terms.append(slack)


    # No solapes mismo empleado/mismo día
    by_day = defaultdict(list)
    for d in dem:
        by_day[d.date].append(d)
    for day in sorted(by_day.keys()):
        lst = sorted(by_day[day], key=lambda z: (_t2m(z.start), _t2m(z.end)))
        for i in range(len(lst)):
            for j in range(i+1, len(lst)):
                if overlap(lst[i], lst[j]):
                    for e in emps_subset:
                        if (e.id, lst[i].id) in X and (e.id, lst[j].id) in X:
                            mdl.Add(X[e.id, lst[i].id] + X[e.id, lst[j].id] <= 1)

    # Máx. 9h/día
    for e in emps_subset:
        for dday in week:
            todays = [dm for dm in dem if dm.date == dday and (e.id, dm.id) in X]
            if todays:
                mdl.Add(sum(duration_min(dm) * X[e.id, dm.id] for dm in todays) <= MAX_HOURS_PER_DAY * 60)
    # 4b) Tope de días trabajados/semana (duro)
    add_max_days_worked_per_week(mdl, emps_subset, dem, X, week, max_days=MAX_DAYS_PER_WEEK)

    # 4c) Balanceo suave en días override (asignación libre)
    balance_term = add_balance_override_workload_soft(
        mdl, emps_subset, dem, X, week, overrides, weight=WEIGHT_BALANCE_OVERRIDE
    )



    # Reglas de bloques / US / mínimos
    add_max2_blocks_per_day(mdl, emps_subset, dem, X)
    add_min_split_gap_usershift_windows(mdl, emps_subset, dem, X, MIN_HOURS_BETWEEN_SPLIT)
    add_min_per_contiguous_block_free_mode(mdl, emps_subset, dem, X, overrides, MIN_SHIFT_DURATION_HOURS)
    add_min_per_contiguous_block_global_enforced(mdl, emps_subset, dem, X, overrides, MIN_SHIFT_DURATION_HOURS)
    add_usershift_must_cover_if_possible_with_overrides(mdl, emps_subset, dem, X, overrides)
    add_shifttype_must_cover_if_possible(mdl, emps_subset, dem, X, overrides)
    add_anchor_must_cover_two_starts(mdl, emps_subset, dem, X, overrides)

    # Mantener preferencia por cubrir dentro de UserShift (y obligación en inicios de ventana si procede)
    add_usershift_must_cover_if_possible_with_overrides(mdl, emps_subset, dem, X, overrides)

    # ---------- OBJETIVO ----------
    # 1) Cobertura ponderada
    weights = {d.id: (WEIGHT_ULTRA_SLOT0 if d.slot_index == 0
                      else (WEIGHT_SHORT_SLOT if duration_min(d) <= 15 else 1000))
               for d in dem}
    total_unmet_weighted = sum(weights[d.id] * unmet[d.id] for d in dem)

    # 2) Penalización por salir de ventana US (si aplica)
    usershift_penalty = build_usershift_window_penalty(mdl, emps_subset, dem, X, overrides)
    shifttype_penalty = build_shifttype_window_penalty(mdl, emps_subset, dem, X, overrides)    # 2bis) **NUEVO**: regla suave de máx. 2 días libres en días de negocio
    penalty_days_off, meta_days_off = add_max_two_days_off_soft(mdl, emps_subset, dem, X)
    
    # 3) **NUEVO**: en modo libre, preferir "especialistas" (menos roles)
    #    Peso pequeño para romper empates sin sacrificar cobertura.
    WEIGHT_SPECIALIST_FREE = 100
    specialist_terms = []
    for e in emps_subset:
        role_pen = len(getattr(e, "roles", [])) or 999
        for d in dem:
            if (e.id, d.id) in X and (e.id, d.date) in overrides:
                specialist_terms.append(role_pen * X[e.id, d.id])
    specialist_penalty = sum(specialist_terms) if specialist_terms else 0
    # Balanceo en asignación libre (overrides): minimiza desigualdad de minutos entre personas
    fair_free_penalty = build_free_mode_balance_penalty(mdl, emps_subset, dem, X, overrides)
    fair_free_days_penalty = build_free_mode_balance_days_penalty(mdl, emps_subset, dem, X, overrides)
    fair_free_days_L1 = build_free_mode_balance_days_L1_penalty(mdl, emps_subset, dem, X, overrides)
    anchor_pref_penalty = build_usershift_anchor_start_preference(mdl, emps_subset, dem, X, overrides)
    # Empujar a que asigne antes a restringidos que a libres (override)
    WEIGHT_FREE_OVERRIDE_LAST = 1500  # súbelo si aún “prefiere” libres
    free_override_penalty = sum(
        X[e.id, d.id]
        for e in emps_subset
        for d in dem
        if ((e.id, d.date) in overrides) and ((e.id, d.id) in X)
    )





    mdl.Minimize(
        total_unmet_weighted
        + usershift_penalty
        + shifttype_penalty
        + WEIGHT_SPECIALIST_FREE * specialist_penalty
        + WEIGHT_FAIR_FREE * fair_free_penalty
        + WEIGHT_FAIR_FREE_DAYS * fair_free_days_penalty
        + WEIGHT_FAIR_FREE_DAYS_L1 * fair_free_days_L1
        + WEIGHT_US_ANCHOR_START * anchor_pref_penalty   # ← NUEVO
        + WEIGHT_FREE_OVERRIDE_LAST * free_override_penalty

    )

    # ---------- Resolver ----------
    sol = cp_model.CpSolver()
    sol.parameters.random_seed = 0
    sol.parameters.num_search_workers = 1
    sol.parameters.max_time_in_seconds = 60
    status = sol.Solve(mdl)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise ScheduleGenerationError("Subfase infactible")

    # ---------- Extraer resultados ----------
    out = defaultdict(list)
    coverage_stats = {}
    remaining_demands = []

    for d in dem:
        covered = sum(1 for e in emps_subset if (e.id, d.id) in X and sol.Value(X[e.id, d.id]))
        u = sol.Value(unmet[d.id])
        coverage_stats[d.id] = {
            "demand": d,
            "covered": covered,
            "unmet": u,
            "coverage_pct": round((covered / d.need) * 100, 1) if d.need > 0 else 100
        }
        if u > 0:
            remaining_demands.append(Demand((d.id, d.date, d.wsid, d.wsname, d.start, d.end, u)))

        for e in emps_subset:
            if (e.id, d.id) in X and sol.Value(X[e.id, d.id]):
                out[d.date].append((e, d))

    days_off_diag = build_days_off_diagnostics(sol, meta_days_off, emps_subset, dem)
    return out, coverage_stats, remaining_demands, days_off_diag


# ───────── GREEDY FALLBACK ─────────
def greedy_fallback(emps: List[Emp], dem: List[Demand], week: List[date],
                    overrides: Set[Tuple[str, date]]):
    """
    Greedy con prioridad a días con UserShift (si no están en override).
    - Intenta formar cadenas contiguas ≥ MIN_SHIFT_DURATION_HOURS dentro de ventanas válidas.
    - Si falla, asigna trozos sueltos y al cierre filtra: bloques < MIN_SHIFT_DURATION_HOURS
      y gaps < MIN_HOURS_BETWEEN_SPLIT (salvo override).
    - Respeta 9h/día y limita implícitamente a máx. 2 bloques/día con el filtrado.
      (La regla semanal de 'máx 2 días off' se garantiza en CP-SAT; aquí se prioriza factibilidad/cobertura.)
    """
    assign = defaultdict(list)
    used_any = defaultdict(lambda: defaultdict(list))   # emp -> date -> [(s,e)]
    used_by_ws = defaultdict(lambda: defaultdict(lambda: defaultdict(list)))  # emp -> date -> wsid -> [(s,e)]
    days_worked = defaultdict(set)
    def _can_take_day(emp_id: str, dday: date) -> bool:
        # Si ya trabaja ese día, ok; si no, solo si lleva < 6 días
        return (dday in days_worked[emp_id]) or (len(days_worked[emp_id]) < MAX_DAYS_PER_WEEK)
    def _free_days_so_far(emp_id: str) -> int:
        cnt = 0
        for dday, intervals in used_any[emp_id].items():
            if (emp_id, dday) in overrides and intervals:
                cnt += 1
        return cnt


    def _free_minutes_so_far(emp_id: str) -> int:
        tot = 0
        for dday, intervals in used_any[emp_id].items():
            if (emp_id, dday) in overrides:  # solo días en libre
                for a, b in intervals:
                    tot += (b - a)
        return tot

    remaining = {d.id: d.need for d in dem}

    dem_sorted = sorted(
        dem,
        key=lambda d: (d.date, str(d.wsid), _t2m(d.start), _t2m(d.end if d.end != time(0, 0) else time(23, 59)))
    )
    by_day = defaultdict(list)
    for dm in dem_sorted:
        by_day[dm.date].append(dm)

    for e in emps:
        for day in sorted(by_day.keys()):
            if (e.id, day) in overrides:
                continue
            # 🚫 Día libre (RT0) o AUSENTE → saltar
            if e.off(day) or e.absent_day(day):
                continue

            dow = day.weekday()
            if dow not in getattr(e, "us_two_starts_dow", set()):
                continue
            wins = sorted(e.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1])))
            for (w_s, w_e) in wins:
                # busca una demanda que arranque exactamente en w_s y que e pueda cubrir
                cand = next((dm for dm in by_day[day]
                             if dm.start == w_s and e.can(dm.wsid) and remaining[dm.id] > 0), None)
                if not _can_take_day(e.id, day):
                    continue

                if not cand:
                    continue
                s = _t2m(cand.start)
                e_min = _t2m(cand.end if cand.end != time(0,0) else time(23,59))
                if not _has_overlap(used_any[e.id][day], s, e_min):
                    assign[day].append((e, cand))
                    used_any[e.id][day].append((s, e_min))
                    used_any[e.id][day].sort()
                    # (opcional pero recomendable, coherencia con el resto del greedy)
                    used_by_ws[e.id][day][cand.wsid] = merge_intervals(
                        used_by_ws[e.id][day][cand.wsid] + [(s, e_min)]
                    )
                    days_worked[e.id].add(day)
                    remaining[cand.id] -= 1
                    if ASCII_LOGS:
                        print(f"[GREEDY-SEED-2STARTS] {e.name} {day} comienza en {w_s.strftime('%H:%M')}")
                    # tras el print("[GREEDY-SEED-2STARTS] ...")
                    min_block = MIN_SHIFT_DURATION_HOURS * 60
                    win_end_min = _t2m(w_e if w_e != time(0,0) else time(23,59))

                    # construye el grupo de ese puesto en ese día, ordenado
                    group = sorted(
                        [dm2 for dm2 in by_day[day] if dm2.wsid == cand.wsid],
                        key=lambda d: (_t2m(d.start), _t2m(d.end if d.end != time(0,0) else time(23,59)))
                    )
                    # índice del segmento sembrado
                    try:
                        start_idx = next(i for i, g in enumerate(group) if g.id == cand.id)
                    except StopIteration:
                        start_idx = None

                    # intenta encadenar contiguamente hasta alcanzar 3h dentro de la misma ventana US
                    if start_idx is not None:
                        acc_start = s
                        acc_end = e_min
                        k = start_idx + 1
                        while k < len(group) and (acc_end - acc_start) < min_block:
                            nxt = group[k]
                            if remaining[nxt.id] <= 0:
                                k += 1; continue
                            nxt_s = _t2m(nxt.start)
                            nxt_e = _t2m(nxt.end if nxt.end != time(0,0) else time(23,59))

                            # Debe ser contiguo, no solapar y seguir dentro de la ventana US
                            if nxt_s == acc_end and nxt_e <= win_end_min and not _has_overlap(used_any[e.id][day], nxt_s, nxt_e):
                                assign[day].append((e, nxt))
                                if not _can_take_day(e.id, day):
                                    break

                                used_any[e.id][day].append((nxt_s, nxt_e))
                                used_any[e.id][day].sort()
                                used_by_ws[e.id][day][nxt.wsid] = merge_intervals(
                                    used_by_ws[e.id][day][nxt.wsid] + [(nxt_s, nxt_e)]
                                )
                                days_worked[e.id].add(day)
                                remaining[nxt.id] -= 1
                                acc_end = nxt_e
                            else:
                                break
                            k += 1


    by_day_ws = defaultdict(list)
    for d in dem_sorted:
        by_day_ws[(d.date, d.wsid)].append(d)
    for k in by_day_ws:
        by_day_ws[k].sort(key=lambda d: (_t2m(d.start), _t2m(d.end if d.end != time(0, 0) else time(23, 59))))

    MIN_BLOCK_MIN = MIN_SHIFT_DURATION_HOURS * 60

    def has_overlap(ints, s, e):
        for a, b in ints:
            if not (e <= a or b <= s):
                return True
        return False

    def has_restr_today(e: Emp, d: date) -> bool:
        dow = d.weekday()
        # Tiene restricción si:
        #  - Tiene ventanas de UserShift y NO está en override ese día, o
        #  - Tiene ventanas derivadas de ShiftType ese día
        us_ok = bool(e.user_shift_windows.get(dow, [])) and ((e.id, d) not in overrides)
        st_ok = bool(e.shift_type_windows.get(dow, []))
        return us_ok or st_ok


    def try_build_chain(emp: Emp, group: List[Demand], start_idx: int) -> List[Demand]:
        chosen = []
        dday = group[start_idx].date
        dow = dday.weekday()
        enforced = (emp.id, dday) not in overrides
        wins = sorted(emp.user_shift_windows.get(dow, []), key=lambda w: (_t2m(w[0]), _t2m(w[1]))) if enforced else []
        tmp_used = list(used_any[emp.id][dday])

        def fits_usershift(dm: Demand) -> bool:
            if not enforced:
                return True
            end = dm.end if dm.end != time(0, 0) else time(23, 59)
            for ws, we in wins:
                w_end = we if we != time(0, 0) else time(23, 59)
                if dm.start >= ws and end <= w_end:
                    # [PATCH] sin exigir ShiftType en modo US enforzado
                    return True
            return False

        prev_end = None
        for k in range(start_idx, len(group)):
            dm = group[k]
            if remaining[dm.id] <= 0:
                continue
            if dm.date != dday or dm.wsid is None:
                continue
            if not emp.can(dm.wsid):
                continue
            if enforced:
                if not fits_usershift(dm):
                    continue
            else:
                if not emp.available(dm.date, dm.start, dm.end):
                    continue

            s = _t2m(dm.start)
            e = _t2m(dm.end if dm.end != time(0, 0) else time(23, 59))

            # contigüidad exacta
            if prev_end is not None and s != prev_end:
                break
            # no solape incremental
            if has_overlap(tmp_used, s, e):
                break
            # tope 9h/día
            total_today = sum((b - a) for a, b in tmp_used)
            if total_today + (e - s) > MAX_HOURS_PER_DAY * 60:
                break

            chosen.append(dm)
            tmp_used.append((s, e))
            tmp_used.sort()

            chain_len = (_t2m(chosen[-1].end if chosen[-1].end != time(0, 0) else time(23, 59)) - _t2m(chosen[0].start))
            if chain_len >= MIN_BLOCK_MIN:
                return chosen

            prev_end = e

        return []
    def has_restr_today(e: Emp, d: date) -> bool:
        dow = d.weekday()
        us_ok = bool(e.user_shift_windows.get(dow, [])) and ((e.id, d) not in overrides)
        st_ok = bool(e.shift_type_windows.get(dow, []))
        return us_ok or st_ok

    # Bucle principal
    for (day, wsid), group in by_day_ws.items():
        for idx, dm in enumerate(group):
            if remaining[dm.id] <= 0:
                continue

            # 1) US del día (no override) primero.
            # 2) Si el día del empleado está en override, prioriza MENOS #días_libres_asignados.
            # 3) Luego menos minutos libres acumulados.
            emps_ordered = sorted(
                emps,
                key=lambda ee: (
                    0 if has_restr_today(ee, day) else 1,  # ← RESTRICCIONES primero
                    len(days_worked[ee.id]),
                    (_free_days_so_far(ee.id) if (ee.id, day) in overrides else 10_000),
                    (_free_minutes_so_far(ee.id) if (ee.id, day) in overrides else 10_000_000),
                    len(ee.roles),
                    ee.name,
                ),
            )



            

            for emp in emps_ordered:
                if remaining[dm.id] <= 0:
                    break
                if not emp.can(dm.wsid):
                    continue
                # 🚫 Día libre (RT0) o AUSENTE
                if emp.off(day) or emp.absent_day(day):
                    continue


                enforced = (emp.id, day) not in overrides
                if not enforced:
                    if not emp.available(dm.date, dm.start, dm.end):
                        continue
                if not _can_take_day(emp.id, day):
                    continue
                       
                # 1) intentar cadena contigua ≥ MIN_SHIFT_DURATION_HOURS
                chain = try_build_chain(emp, group, idx)
                if chain:
                    for dmx in chain:
                        if remaining[dmx.id] <= 0:
                            continue
                        ss = _t2m(dmx.start)
                        ee = _t2m(dmx.end if dmx.end != time(0, 0) else time(23, 59))
                        assign[day].append((emp, dmx))
                        used_any[emp.id][day].append((ss, ee))
                        used_any[emp.id][day].sort()
                        used_by_ws[emp.id][day][dmx.wsid] = merge_intervals(
                            used_by_ws[emp.id][day][dmx.wsid] + [(ss, ee)]
                        )
                        days_worked[emp.id].add(day)
                        remaining[dmx.id] -= 1
                    continue

                # 2) trozo suelto
                ss = _t2m(dm.start)
                ee = _t2m(dm.end if dm.end != time(0, 0) else time(23, 59))
                
                if has_overlap(used_any[emp.id][day], ss, ee):
                    continue

                total_today = sum((b - a) for a, b in used_any[emp.id][day])
                if total_today + (ee - ss) > MAX_HOURS_PER_DAY * 60:
                    continue

                if enforced and not _fits_usershift_enforced(emp, dm):
                    continue
                if not _can_take_day(emp.id, day):
                    continue

                assign[day].append((emp, dm))
                used_any[emp.id][day].append((ss, ee))
                used_any[emp.id][day].sort()
                used_by_ws[emp.id][day][dm.wsid] = merge_intervals(
                    used_by_ws[emp.id][day][dm.wsid] + [(ss, ee)]
                )
                days_worked[emp.id].add(day)
                remaining[dm.id] -= 1

    # Post-proceso: filtrar bloques < MIN_SHIFT_DURATION_HOURS y gaps inválidos; máx 2 bloques
    for day in list(assign.keys()):
        filtered = _filter_blocks_min4_and_gap_global(
            assign[day],
            overrides,
            MIN_SHIFT_DURATION_HOURS,
            MIN_HOURS_BETWEEN_SPLIT
        )
        assign[day] = filtered
    # Recalcular días realmente trabajados tras el filtrado
    days_worked = defaultdict(set)
    for dday, pairs in assign.items():
        for emp, _ in pairs:
            days_worked[emp.id].add(dday)


    # Estadísticas de cobertura
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

def _fits_usershift_enforced(emp: Emp, dm: Demand) -> bool:
    dow = dm.date.weekday()
    end = dm.end if dm.end != time(0,0) else time(23,59)
    if not emp.user_shift_windows.get(dow): return False
    in_any = any(dm.start >= ws and end <= (we if we != time(0,0) else time(23,59))
                 for ws, we in emp.user_shift_windows[dow])
    if not in_any: return False
    # [PATCH] No condicionamos por shift_type cuando el día está usershift_enforced
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

def _filter_blocks_min4_and_gap(assigns_day_pairs, overrides, min_block_hours: int, min_gap_hours: int, daily_min_hours_override: int = 3):
    """
    Empleado/día:
      - Si está en free_mode (override) y trabaja ese día:
          · total ≥ daily_min_hours_override (sumando TODOS los puestos).
          · si hay descansos, cada descanso ≥ min_gap_hours; de lo contrario, nos quedamos con el bloque más largo.
      - Si NO está en free_mode: mantener bloques ≥ min_block_hours y exigir gap.
    """
    min_block = min_block_hours * 60
    by_emp_ws = defaultdict(list)  # (emp.id, wsid) -> [(s,e,emp,dm)]
    for emp, dm in assigns_day_pairs:
        if dm.wsid is None:
            by_emp_ws[(emp.id, None)].append((0, 0, emp, dm))
            continue
        s = _t2m(dm.start)
        e = _t2m(dm.end if dm.end != time(0,0) else time(23,59))
        by_emp_ws[(emp.id, dm.wsid)].append((s, e, emp, dm))

    def _merge_sorted_local(intervals):
        if not intervals: return []
        intervals = sorted(intervals)
        merged = [intervals[0]]
        for s,e in intervals[1:]:
            ls,le = merged[-1]
            if s <= le: merged[-1] = (ls, max(le, e))
            else: merged.append((s, e))
        return merged

    def _respect_split_gap_local(merged, min_gap_hours: int):
        if not min_gap_hours or min_gap_hours <= 0: 
            return True
        min_gap = min_gap_hours * 60
        for i in range(len(merged) - 1):
            gap = merged[i+1][0] - merged[i][1]
            if 0 < gap < min_gap:
                return False
        return True

    filtered = []

    for (eid, wsid), rows in by_emp_ws.items():
        if wsid is None:
            for _, _, emp, dm in rows:
                filtered.append((emp, dm))
            continue

        rows.sort(key=lambda r: (r[0], r[1]))
        merged_bounds = _merge_sorted_local([(s, e) for (s, e, _, _) in rows])

        any_dm = rows[0][3]
        day_override = (eid, any_dm.date) in overrides

        if day_override:
            strong_blocks = merged_bounds[:]
            if not _respect_split_gap_local(strong_blocks, min_gap_hours):
                longest = max(strong_blocks, key=lambda b: (b[1]-b[0]))
                strong_blocks = [longest]
        else:
            strong_blocks = [(s, e) for (s, e) in merged_bounds if (e - s) >= min_block]
            if not strong_blocks:
                continue
            if not _respect_split_gap_local(strong_blocks, min_gap_hours):
                longest = max(strong_blocks, key=lambda b: (b[1]-b[0]))
                strong_blocks = [longest]

        if day_override:
            total_day_min = sum(e - s for (s, e) in strong_blocks)
            if total_day_min > 0 and total_day_min < daily_min_hours_override * 60:
                continue

        for s, e in strong_blocks:
            for s0, e0, emp, dm in rows:
                if s0 >= s and e0 <= e:
                    filtered.append((emp, dm))

    return filtered

def _filter_blocks_min4_and_gap_global(assigns_day_pairs, overrides,
                                       min_block_hours: int, min_gap_hours: int):
    """
    Filtro post-greedy GLOBAL por día/empleado (mezcla todos los puestos):
      - Bloques contiguos >= min_block_hours (3h).
      - Si se parte el bloque: cada descanso >= min_gap_hours (3h); si no, conservar el BLOQUE más largo.
      - En libre: si total día < 3h, descartar.
    """
    min_block = int(min_block_hours * 60)
    gap_min = int(min_gap_hours * 60)

    by_emp = defaultdict(list)  # eid -> [(s,e,emp,dm)]
    for emp, dm in assigns_day_pairs:
        s = _t2m(dm.start)
        e = _t2m(dm.end if dm.end != time(0,0) else time(23,59))
        by_emp[emp.id].append((s, e, emp, dm))

    out = []
    for eid, rows in by_emp.items():
        if not rows:
            continue
        rows.sort(key=lambda r: (r[0], r[1]))
        # Coalesce global por día:
        merged = _merge_sorted([(s, e) for (s, e, _, _) in rows])

        # Detecta descansos pequeños
        ok_gaps = True
        for i in range(len(merged)-1):
            if 0 < (merged[i+1][0] - merged[i][1]) < gap_min:
                ok_gaps = False
                break

        # En libre, si total < 3h -> descartar todo
        any_dm = rows[0][3]
        free_mode = (eid, any_dm.date) in overrides
        total_min = sum(b - a for a, b in merged)

        if free_mode and total_min < min_block:
            continue

        strong_blocks = []
        if ok_gaps:
            strong_blocks = [(s, e) for (s, e) in merged if (e - s) >= min_block]
            # En días enforzados: si ningún bloque llega al mínimo, no dejamos nada
            if not strong_blocks:
                continue

        else:
            # si hay gap corto, quedarse con el bloque más largo
            if merged:
                strong_blocks = [max(merged, key=lambda ab: (ab[1]-ab[0]))]

        # reconstruir asignaciones dentro de los strong_blocks
        for s, e in strong_blocks:
            for s0, e0, emp, dm in rows:
                if s0 >= s and e0 <= e:
                    out.append((emp, dm))

    return out


def _merge_sorted(intervals):
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged


def _filter_free_mode_total_and_gaps(assigns_day_pairs, overrides, min_total_hours: int, gap_hours: int):
    by_emp = defaultdict(list)
    for emp, dm in assigns_day_pairs:
        s = _t2m(dm.start)
        e = _t2m(dm.end if dm.end != time(0,0) else time(23,59))
        by_emp[emp.id].append((s, e, emp, dm))
    out = []
    MIN_TOT = min_total_hours * 60
    GAP = gap_hours * 60
    for eid, rows in by_emp.items():
        rows.sort(key=lambda r: (r[0], r[1]))
        merged = merge_intervals([(s, e) for (s, e, _, _) in rows])
        total = sum(b - a for a, b in merged)
        any_dm = rows[0][3]
        free_mode_today = (eid, any_dm.date) in overrides
        if not free_mode_today:
            out.extend([(emp, dm) for _, _, emp, dm in rows])
            continue
        if total == 0 or total < MIN_TOT:
            continue
        ok_gaps = True
        for i in range(len(merged) - 1):
            gap = merged[i+1][0] - merged[i][1]
            if 0 < gap < GAP:
                ok_gaps = False
                break
        if ok_gaps:
            out.extend([(emp, dm) for _, _, emp, dm in rows])
        else:
            longest = max(merged, key=lambda ab: (ab[1]-ab[0]))
            for s0, e0, emp, dm in rows:
                if s0 >= longest[0] and e0 <= longest[1]:
                    out.append((emp, dm))
    return out

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
    """
    CA3: Etiquetas de salida
    - "C": si el turno termina en la ÚLTIMA franja del DÍA (global, no por puesto).
    - "BT": en los demás casos.
    - Si el empleado tiene un Tipo de Turno con hora de salida fija para ese día,
      el caller deberá mostrar la hora exacta (esto se gestiona en generate()).
    """
    if (emp.id, dm.id) in fixed_ids:
        return ""
    # Ignorar pseudo-demandas sin wsid
    same_day = [d for e2, d in assigns_day if d.date == dm.date and d.wsid is not None]
    if not same_day:
        return "BT"
    latest_end = max(d.end if d.end != time(0,0) else time(23,59) for d in same_day)
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
    sched, relaxed_groups, days_off_diag = solve(emps, demands, week, overrides, min_hours_required)

    # ===== NUEVO: POST-PROCESO HÍBRIDO 0.5 =====
    # Construir coverage_stats para el post-proceso
    coverage_stats = {}
    for dm in demands:
        covered = sum(1 for e2, d2 in sched.get(dm.date, []) if d2.id == dm.id)
        coverage_stats[dm.id] = {
            "demand": dm,
            "met": covered,
            "unmet": max(0, dm.need - covered),
            "covered": covered,
            "coverage_pct": round((covered / dm.need) * 100, 1) if dm.need > 0 else 100,
            "employees": []
        }
    
    apply_hybrid_05_postprocess(
        emps=emps,
        demands=demands,
        week=week,
        sched=sched,
        coverage_stats=coverage_stats,
        overrides=overrides,
    )
    # ===== FIN POST-PROCESO HÍBRIDO =====

    for d, lst in fixed.items(): sched[d].extend(lst)
    fixed_ids = {(e.id, dm.id) for lst in fixed.values() for e, dm in lst}

    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id": uid(), "wsid": None, "wsname": "AUSENCIA",
                    "start": time(0,0), "end": time(0,0), "date": d,
                    "shift_type": None,  
                })()
                sched[d].append((emp, pseudo_dm))

    usershift_assignment_report, usershift_windows_report = build_usershift_reports(emps, week, usershift_plan, sched)

    total_req = sum(dm.need for dm in demands) + len(fixed_ids)
    total_ass = sum(len(v) for v in sched.values())

    overrides_list = [{"employee_id": str(eid),
                       "employee_name": next((e.name for e in emps if e.id == eid), ""),
                       "date": d.isoformat()} for (eid, d), v in usershift_plan.items() if v["mode"] == "free_mode"]

    relaxed_list = [{"date": gdate.isoformat(), "workstation_id": str(wsid)}
                    for (gdate, wsid) in sorted(relaxed_groups, key=lambda x: (x[0], str(x[1])))]
    latest_end_by_wsid = build_latest_end_map_from_demands(demands)
    latest_end_by_day = build_latest_end_of_day_map(demands)
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
            "usershift_windows_report": usershift_windows_report,
            "days_off_violations": days_off_diag
        },
        "latest_end_by_wsid": latest_end_by_wsid,
        "latest_end_of_day": latest_end_by_day,
        "schedule": {}
    }
    

    for d in week:
        k = d.isoformat(); res["schedule"][k] = []
        for emp, dm in sorted(sched.get(d, []), key=lambda x: (x[0].name, x[1].wsname, _t2m(x[1].start))):
            day_key = d.isoformat()
            latest_end_min = latest_end_by_day.get(day_key)
            cur_end_min = _t2m(dm.end if dm.end != time(0,0) else time(23,59))

            
            # Etiqueta según CA3: hora fija si aplica, sino C/BT global por día
            end_label = None
            enforced_us = (emp.id, d) not in overrides  # día con UserShift enforzado

            # Hora exacta si ShiftType tiene fin fijo
            st = getattr(dm, 'shift_type', None)
            if st and st.get('end_time') and st['end_time'] != time(0,0):
                end_label = st['end_time'].strftime('%H:%M')            
            ws_latest_map = res.get("latest_end_by_wsid", {}).get(day_key, {})
            ws_latest_end_min = ws_latest_map.get(str(dm.wsid)) if dm.wsid is not None else None
            cur_end_min = _t2m(dm.end if dm.end != time(0,0) else time(23,59))

            # ¿Ese día es UserShift enforzado para este empleado?
            enforced_us = (emp.id, d) not in overrides  # ya lo tienes calculado arriba

            # Lógica de observación
            if dm.wsid is None:
                obs = "ABS" if emp.abs_reason.get(d) == "VAC" else "ABS"
            else:
                # Si es UserShift enforzado y termina al final del día del WS → observación vacía
                if enforced_us and ws_latest_end_min is not None and cur_end_min == ws_latest_end_min:
                    obs = ""
                # Si tiene hora fija por ShiftType
                elif st and st.get('end_time') and st['end_time'] != time(0,0):
                    obs = st['end_time'].strftime('%H:%M')
                # Caso normal: C si termina al final del día, BT en otros casos
                else:
                    obs = "C" if (ws_latest_end_min is not None and cur_end_min == ws_latest_end_min) else "BT"

            
            res["schedule"][k].append({
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "workstation_id": (str(dm.wsid) if dm.wsid is not None else None),
                "workstation_name": dm.wsname,
                "start_time": (dm.start.strftime("%H:%M") if dm.start else None),
                "end_time": (dm.end.strftime("%H:%M") if dm.end else None),
                "observation": obs
            })

    return res, sched, emps, week, fixed_ids

def generate_flexible(week_start: date):
    emps, demands, tpl, week, fixed, shift_types, min_hours_required = load_data(week_start)
    overrides, usershift_plan = plan_usershift_day_modes(emps, demands, week)

    # ── NUEVO: traza legible de UserShifts
    debug_print_usershifts(emps, week, usershift_plan)

    # 1) Intento CP-SAT flexible
    try:
        sched, coverage_stats, days_off_diag = solve_flexible(emps, demands, week, overrides, min_hours_required)
        recheck_fill_unmet(emps, demands, week, sched, coverage_stats, overrides)
        solved_by = "cp_sat"
    except ScheduleGenerationError:
        sched, coverage_stats = greedy_fallback(emps, demands, week, overrides)
        solved_by = "greedy_fallback"
        days_off_diag = []
    
    # 1.bis) POST-PROCESO HÍBRIDO 0,5
    # Aquí SÍ se ejecuta siempre, con el horario final (CP-SAT o greedy),
    # y respeta todas las restricciones previas, relajando solapamiento solo para parejas 0,5 válidas.
    apply_hybrid_05_postprocess(
        emps=emps,
        demands=demands,
        week=week,
        sched=sched,
        coverage_stats=coverage_stats,
        overrides=overrides,
    )

     

    for emp in emps:
        for d in emp.absent:
            if week_start <= d <= week[-1]:
                pseudo_dm = type("Pseudo", (), {
                    "id": uid(), "wsid": None, "wsname": "AUSENCIA",
                    "start": time(0,0), "end": time(0,0), "date": d,
                    "shift_type": None,  # ← para evitar atributos faltantes
                })()
                sched[d].append((emp, pseudo_dm))

    usershift_assignment_report, usershift_windows_report = build_usershift_reports(emps, week, usershift_plan, sched)

    total_req = sum(dm.need for dm in demands)
    total_cov = sum(s["covered"] for s in coverage_stats.values())
    total_unmet = sum(s["unmet"] for s in coverage_stats.values())

    overrides_list = [{"employee_id": str(eid),
                       "employee_name": next((e.name for e in emps if e.id == eid), ""),
                       "date": d.isoformat()} for (eid, d), v in usershift_plan.items() if v["mode"] == "free_mode"]
    latest_end_by_wsid = build_latest_end_map_from_demands(demands)
    latest_end_by_day = build_latest_end_of_day_map(demands)
    res = {
        "template": tpl,
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
        k = d.isoformat(); 
        res["schedule"][k] = []
        for emp, dm in sorted(sched.get(d, []), key=lambda x: (x[0].name, x[1].wsname, _t2m(x[1].start))):
            day_key = d.isoformat()
            latest_end_min = latest_end_by_day.get(day_key)
            cur_end_min = _t2m(dm.end if dm.end != time(0,0) else time(23,59))

            end_label = None
            enforced_us = (emp.id, d) not in overrides

            if dm.shift_type and (dm.shift_type.get('end_time') and dm.shift_type['end_time'] != time(0,0)):
                end_label = dm.shift_type['end_time'].strftime('%H:%M')
            ws_latest_map = res.get("latest_end_by_wsid", {}).get(day_key, {})
            ws_latest_end_min = ws_latest_map.get(str(dm.wsid)) if dm.wsid is not None else None
            cur_end_min = _t2m(dm.end if dm.end != time(0,0) else time(23,59))

            enforced_us = (emp.id, d) not in overrides

            if dm.wsid is None:
                obs = "ABS" if emp.abs_reason.get(d) == "VAC" else "ABS"
            else:
                if enforced_us and ws_latest_end_min is not None and cur_end_min == ws_latest_end_min:
                    obs = ""
                elif dm.shift_type and (dm.shift_type.get('end_time') and dm.shift_type['end_time'] != time(0,0)):
                    obs = dm.shift_type['end_time'].strftime('%H:%M')
                else:
                    obs = "C" if (ws_latest_end_min is not None and cur_end_min == ws_latest_end_min) else "BT"

            res["schedule"][k].append({
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "workstation_id": (str(dm.wsid) if dm.wsid is not None else None),
                "workstation_name": dm.wsname,
                "start_time": (dm.start.strftime("%H:%M") if dm.start else None),
                "end_time": (dm.end.strftime("%H:%M") if dm.end else None),
                "observation": obs
            })
    
    return res, sched, emps, week, set()

# ───────── Post-proceso UserShift estricto + reasignación ─────────

def _seg_minutes(dm) -> int:
    """Duración (min) de un segmento de demanda."""
    if dm is None or dm.start is None or dm.end is None:
        return 0
    end = dm.end
    # En la BD fin 00:00 significa 24:00 del mismo día
    if end == time(0, 0):
        end = time(23, 59)
    return max(0, (end.hour * 60 + end.minute) - (dm.start.hour * 60 + dm.start.minute))


def _merge_windows_simple(wins: list[tuple[time, time]]) -> list[tuple[time, time]]:
    """Une ventanas [start,end] solapadas; asume mismo día."""
    if not wins:
        return []
    wins = sorted(wins, key=lambda w: (w[0], w[1]))
    merged: list[list[time, time]] = [[wins[0][0], wins[0][1]]]
    for s, e in wins[1:]:
        s0, e0 = merged[-1]
        if s <= e0:
            if e > e0:
                merged[-1][1] = e
        else:
            merged.append([s, e])
    return [(s, e) for s, e in merged if s < e]


def _effective_windows_for(emp, d: date) -> list[tuple[time, time]]:
    """
    Ventanas efectivas para validar asignaciones en el post-proceso:
    - Si hay user_shift_windows para ese DOW: se usan como base.
    - Si no, se usan window + shift_type_windows.
    - Se agregan ventanas excepcionales por fecha (exc).
    """
    dow = d.weekday()
    wins: list[tuple[time, time]] = []

    us_wins = getattr(emp, "user_shift_windows", {}).get(dow, [])
    if us_wins:
        wins.extend(us_wins)
    else:
        wins.extend(getattr(emp, "window", {}).get(dow, []) or [])
        wins.extend(getattr(emp, "shift_type_windows", {}).get(dow, []) or [])

    wins.extend(getattr(emp, "exc", {}).get(d, []) or [])

    norm: list[tuple[time, time]] = []
    for s, e in wins:
        if e == time(0, 0):
            e = time(23, 59)
        if s < e:
            norm.append((s, e))

    return _merge_windows_simple(norm)


def _can_take_segment_usershift_safe(
    emp,
    d: date,
    dm,
    by_emp_day: dict[tuple[str, date], list],
    week_minutes: dict[str, int],
) -> bool:
    """
    Verifica si 'emp' puede recibir 'dm' en 'd' sin romper:
      - Ausencias / días libres / no_assign_by_date
      - Rol del puesto
      - Ventanas horarias efectivas
      - Tope de horas/día (MAX_HOURS_PER_DAY)
      - No solapar con bloques ya asignados
      - Coherencia con UserShift estricto (si aplica):
            si existe anchor para el día, el earliest start (incluyendo dm) debe ser == anchor.
    """
    # Ausencias / días prohibidos
    if getattr(emp, "no_assign_by_date", None) and d in emp.no_assign_by_date:
        return False
    if emp.off(d) or emp.absent_day(d):
        return False

    # Rol
    if dm.wsid is not None and not emp.can(dm.wsid):
        return False

    # Duración
    seg_min = _seg_minutes(dm)
    if seg_min <= 0:
        return False

    # Ventanas efectivas
    wins = _effective_windows_for(emp, d)
    if wins:
        end = dm.end if dm.end != time(0, 0) else time(23, 59)
        ok = any(dm.start >= ws and end <= (we if we != time(0, 0) else time(23, 59))
                 for ws, we in wins)
        if not ok:
            return False

    # No solapar con su horario actual
    existing = by_emp_day.get((emp.id, d), [])
    end = dm.end if dm.end != time(0, 0) else time(23, 59)
    for cur in existing:
        c_end = cur.end if cur.end != time(0, 0) else time(23, 59)
        if not (end <= cur.start or dm.start >= c_end):
            return False

    # Tope horas por día (usa MAX_HOURS_PER_DAY seteado en load_data; fallback 9h)
    day_min = sum(_seg_minutes(cur) for cur in existing)
    max_day_min = (globals().get("MAX_HOURS_PER_DAY") or 9) * 60
    if day_min + seg_min > max_day_min:
        return False

    # Coherencia con UserShift: si hay anchor para ese día, el earliest debe ser EXACTO
    anchor_by_date = getattr(emp, "user_shift_anchor_by_date", {})
    anchor = anchor_by_date.get(d)
    has_us = getattr(emp, "has_us_row_by_dow", {}).get(d.weekday(), False)

    if anchor:
        all_segments = existing + [dm]
        earliest = min(all_segments, key=lambda x: (x.start, x.end)).start
        if earliest != anchor:
            return False
    elif has_us:
        # Tiene UserShift pero sin anchor (modo libre); se permite mientras cumpla ventanas.
        pass

    return True


def enforce_usershift_exact_and_reassign(emps, week, sched):
    """
    1) Para cada empleado/día con UserShift ANCLADO (user_shift_anchor_by_date):
         - Si tiene asignaciones y su primer bloque NO inicia en el anchor,
           se eliminan TODAS sus asignaciones de ese día.
    2) Cada segmento liberado se intenta reasignar a otro empleado compatible:
         - Respeta `_can_take_segment_usershift_safe`.
         - Prioriza:
             a) Empleados SIN anchor estricto ese día (modo libre).
             b) Luego, quienes tengan MENOS minutos totales en la semana.
    Modifica `sched` in-place (dict[date] -> list[(Emp, Demand)]).
    """
    if not sched:
        return

    from collections import defaultdict

    emap = {e.id: e for e in emps}

    # Índices iniciales
    by_emp_day: dict[tuple[str, date], list] = defaultdict(list)
    week_minutes: dict[str, int] = defaultdict(int)

    for d, assigns in sched.items():
        for emp, dm in assigns:
            by_emp_day[(emp.id, d)].append(dm)
            week_minutes[emp.id] += _seg_minutes(dm)

    freed: list[tuple[date, object]] = []

    # 1) Limpiar días con UserShift mal alineado
    for (eid, d), dms in list(by_emp_day.items()):
        if not dms:
            continue
        emp = emap.get(eid)
        if not emp:
            continue

        anchor_by_date = getattr(emp, "user_shift_anchor_by_date", {})
        anchor = anchor_by_date.get(d)
        if not anchor:
            continue  # ese día no es US estricto

        if getattr(emp, "no_assign_by_date", None) and d in emp.no_assign_by_date:
            # Si por alguna razón tiene asignaciones, se limpian
            if dms:
                if ASCII_LOGS:
                    print(f"[US-STRICT] {emp.name} {d} no_assign_by_date con asignaciones ⇒ se limpian.")
                new_list = [(e2, dm) for (e2, dm) in sched[d] if e2.id != eid]
                for _dm in dms:
                    freed.append((d, _dm))
                    week_minutes[eid] -= _seg_minutes(_dm)
                sched[d] = new_list
                by_emp_day[(eid, d)] = []
            continue

        earliest_dm = min(dms, key=lambda x: (x.start, x.end))
        # ── Tolerancia de ±60 min para el anchor ──
        # Si la primera asignación arranca dentro de 60 min del anchor,
        # NO se libera el día. Esto evita perder cobertura masivamente
        # por diferencias pequeñas (ej. anchor=10:00, earliest=10:30).
        anchor_min = anchor.hour * 60 + anchor.minute
        earliest_min_val = earliest_dm.start.hour * 60 + earliest_dm.start.minute
        anchor_diff = abs(earliest_min_val - anchor_min)
        US_STRICT_TOLERANCE_MIN = 60  # configurable: 60 min de tolerancia

        if earliest_dm.start != anchor and anchor_diff > US_STRICT_TOLERANCE_MIN:
            # Día con US pero arrancando fuera de tolerancia → se libera TODO ese día para ese empleado
            if ASCII_LOGS:
                print(
                    f"[US-STRICT] {emp.name} {d} anchor={anchor.strftime('%H:%M')} "
                    f"pero earliest={earliest_dm.start.strftime('%H:%M')} (diff={anchor_diff}min > {US_STRICT_TOLERANCE_MIN}min) ⇒ se libera el día completo."
                )
            new_list = []
            for (e2, dm) in sched[d]:
                if e2.id == eid:
                    freed.append((d, dm))
                    week_minutes[eid] -= _seg_minutes(dm)
                else:
                    new_list.append((e2, dm))
            sched[d] = new_list
            by_emp_day[(eid, d)] = []

    if not freed:
        return

    # Recalcular índices tras limpiar
    by_emp_day.clear()
    week_minutes = defaultdict(int)
    for d, assigns in sched.items():
        for emp, dm in assigns:
            by_emp_day[(emp.id, d)].append(dm)
            week_minutes[emp.id] += _seg_minutes(dm)

    # 2) Reasignar segmentos liberados
    for d, dm in freed:
        candidates = []
        for e in emps:
            if not _can_take_segment_usershift_safe(e, d, dm, by_emp_day, week_minutes):
                continue
            anc = getattr(e, "user_shift_anchor_by_date", {}).get(d)
            is_strict = 1 if anc else 0   # primero libres (0), luego con anchor (1)
            candidates.append((is_strict, week_minutes.get(e.id, 0), e.name, e))

        if not candidates:
            if ASCII_LOGS:
                end = dm.end if dm.end != time(0, 0) else time(23, 59)
                print(
                    f"[US-STRICT] Sin candidato para {dm.wsname} {d} "
                    f"{dm.start.strftime('%H:%M')}-{end.strftime('%H:%M')}"
                )
            continue

        candidates.sort()
        chosen = candidates[0][3]

        sched[d].append((chosen, dm))
        by_emp_day[(chosen.id, d)].append(dm)
        week_minutes[chosen.id] += _seg_minutes(dm)

        if ASCII_LOGS:
            end = dm.end if dm.end != time(0, 0) else time(23, 59)
            print(
                f"[US-STRICT] Reasignado {dm.wsname} {d} "
                f"{dm.start.strftime('%H:%M')}-{end.strftime('%H:%M')} a {chosen.name}"
            )



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
def cleanup_null_workstation_schedules(cur, week_start: date, week_end: date) -> int:
    """
    Elimina todos los registros de la tabla Schedules donde WorkstationId es NULL
    para el rango de fechas especificado.
    
    Args:
        cur: Cursor de la conexión a la base de datos
        week_start: Fecha de inicio de la semana
        week_end: Fecha de fin de la semana
    
    Returns:
        int: Número de registros eliminados
    """
    cur.execute(
        '''
        DELETE FROM "Management"."Schedules"
        WHERE "Date" BETWEEN %s AND %s
          AND "WorkstationId" IS NULL
        ''',
        (week_start, week_end),
    )
    deleted_count = cur.rowcount
    
    if ASCII_LOGS and deleted_count > 0:
        print(f"[CLEANUP] Eliminados {deleted_count} registros con WorkstationId NULL")
    
    return deleted_count

@app.route('/api/agenda/save', methods=['POST'])
def save():
    data = request.get_json() or {}
    wk = data.get('week_start')
    force = bool(data.get('force', False))
    flexible = bool(data.get('flexible', True))

    if not wk:
        return jsonify({"error": "Falta week_start"}), 400

    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    we = ws + timedelta(days=6)

    # Token por ejecución (te sirve para comparar versiones)
    token = data.get("token") or f"{ws.isoformat()}|{'flex' if flexible else 'strict'}|{uid()[:8]}"

    # Usuario (para auditoría)
    usuario_id = (
        data.get("usuario_id")
        or data.get("userId")
        or data.get("user_id")
        or "system"
    )

    # 1) Generar horario
    try:
        res, sched, emps, week, fixed_ids = (
            generate_flexible(ws) if flexible else generate(ws)
        )
    except (DatabaseConnectionError, DataNotFoundError) as e:
        return jsonify({"error": str(e)}), 400

    # 2) APLICAR reglas de UserShift estricto + reasignación
    enforce_usershift_exact_and_reassign(emps, week, sched)

    # 3) Logs debug (igual que tenías)
    for d in sorted(sched.keys()):
        javier_raw = [
            (emp.name, dm.wsname, dm.start, dm.end)
            for emp, dm in sched[d]
            if emp.id == "cfb790cc-fd37-4c51-a81b-65caa1859020"
        ]
        if javier_raw:
            print(f"[DEBUG-PRE-COALESCE] {d}: {javier_raw}")

    # Contadores para resumen
    inserted_gaps = 0
    inserted_quality = 0
    sugerencias_generadas = []
    ajustes_ia = []

    # 4) Inserción determinista + HU 1.1 + HU 1.2 + HU 1.3 + HU 1.4 dentro de la transacción (con SAVEPOINT)
    try:
        with conn() as c, c.cursor() as cur:
            # --- Validación existencia semana ---
            cur.execute(
                'SELECT COUNT(*) FROM "Management"."Schedules" '
                'WHERE "Date" BETWEEN %s AND %s',
                (ws, we),
            )
            if cur.fetchone()[0] and not force:
                return jsonify({"error": "Horario ya existe para esa semana"}), 409

            # --- Si force: borrar schedules + gaps/quality/suggestions de la semana ---
            if force:
                cur.execute(
                    'DELETE FROM "Management"."Schedules" '
                    'WHERE "Date" BETWEEN %s AND %s',
                    (ws, we),
                )
                # Borra gaps de esa semana
                cur.execute(
                    'DELETE FROM "Management"."ScheduleGaps" '
                    'WHERE "Date" BETWEEN %s AND %s',
                    (ws, we),
                )
                # Borra quality-shifts de esa semana
                cur.execute(
                    'DELETE FROM "Management"."ScheduleQualityShiftScores" '
                    'WHERE "Date" BETWEEN %s AND %s',
                    (ws, we),
                )
                # Borra sugerencias de esa semana (HU 1.3)
                try:
                    cur.execute(
                        'DELETE FROM "Management"."ScheduleSuggestions" '
                        'WHERE "WeekStart" = %s',
                        (ws,),
                    )
                except Exception:
                    pass  # Si la tabla no existe aún, ignorar
                # Borra predicciones IA de esa semana (HU 1.4)
                try:
                    cur.execute(
                        'DELETE FROM "Management"."AIPredictions" '
                        'WHERE "Token" LIKE %s',
                        (f"{ws.isoformat()}%",),
                    )
                except Exception:
                    pass  # Si la tabla no existe aún, ignorar

            # =========================================================
            # HU 1.1 - EXPLICADOR DE HUECOS (ScheduleGaps)
            # =========================================================
            cur.execute("SAVEPOINT hu11")
            explicaciones = []
            try:
                from services.explicador_huecos import ExplicadorHuecosService, ContextoExplicacion
                from collections import defaultdict
                from datetime import time as _time

                print(f"[HU1.1][SAVE] token={token}")

                # 1) Construir asignaciones_por_empleado desde sched (post usershift)
                asignaciones_por_empleado = defaultdict(list)

                for d0 in sorted(sched.keys()):
                    for emp0, dm0 in sched[d0]:
                        if dm0 is None or dm0.wsid is None:
                            continue

                        ini0 = datetime.combine(d0, dm0.start)
                        fin0 = datetime.combine(d0, dm0.end)

                        if dm0.end == _time(0, 0) or fin0 <= ini0:
                            fin0 = datetime.combine(d0 + timedelta(days=1), dm0.end)

                        asignaciones_por_empleado[emp0.id].append((ini0, fin0, dm0.wsid))

                ctx = ContextoExplicacion(
                    empleados=emps,
                    asignaciones_por_empleado=dict(asignaciones_por_empleado),
                )

                gaps_table = '"Management"."ScheduleGaps"'
                svc = ExplicadorHuecosService(cur, table_name=gaps_table)

                explicaciones = svc.generar_y_guardar(res, ctx, token=token)
                inserted_gaps = len(explicaciones) if explicaciones else 0

                print(f"[HU1.1][DB] inserted={inserted_gaps} into {gaps_table} token={token}")

                cur.execute("RELEASE SAVEPOINT hu11")
            except Exception as e:
                cur.execute("ROLLBACK TO SAVEPOINT hu11")
                cur.execute("RELEASE SAVEPOINT hu11")
                print("[HU1.1] Error (no aborta save):", str(e))
                import traceback
                traceback.print_exc()

            # =========================================================
            # HU 1.2 - PUNTAJE DE CALIDAD POR TURNO (por demanda/slot)
            # Fuente: res["coverage_details"] (demanded/covered/unmet)
            # =========================================================
            cur.execute("SAVEPOINT hu12")
            try:
                import json
                from collections import defaultdict
                from datetime import time as _time

                quality_table = '"Management"."ScheduleQualityShiftScores"'

                # Config (configurable)
                cfg = {
                    "range": [0, 100],
                    "weights": {"coverage": 0.70, "fairness": 0.20, "rules": 0.10},
                    "rules": {"days_off_violation_penalty": 20},
                    "notes": "HU1.2 per demand slot. coverage_details driven."
                }
                w_cov = float(cfg["weights"]["coverage"])
                w_fair = float(cfg["weights"]["fairness"])
                w_rule = float(cfg["weights"]["rules"])

                # ---------- fairness por día (Gini sobre minutos por empleado) ----------
                def _gini(values):
                    vals = [v for v in values if v is not None]
                    if not vals:
                        return 0.0
                    vals = sorted([max(0.0, float(v)) for v in vals])
                    n = len(vals)
                    s = sum(vals)
                    if s == 0:
                        return 0.0
                    acc = 0.0
                    for i, v in enumerate(vals, start=1):
                        acc += i * v
                    return (2.0 * acc) / (n * s) - (n + 1.0) / n

                fairness_by_day = {}
                for d0 in sorted(sched.keys()):
                    mins_by_emp = defaultdict(int)
                    for emp0, dm0 in sched[d0]:
                        if dm0 is None or dm0.wsid is None:
                            continue
                        s_min = _t2m(dm0.start)
                        e_min = _t2m(dm0.end if dm0.end != _time(0, 0) else _time(23, 59))
                        if e_min <= s_min:
                            e_min = 24 * 60
                        mins_by_emp[str(emp0.id)] += (e_min - s_min)

                    g = _gini(list(mins_by_emp.values()))
                    fairness_by_day[d0.isoformat()] = round(max(0.0, 100.0 * (1.0 - g)), 2)

                # ---------- rules por día (heurística con days_off_violations si existe) ----------
                rules_by_day = defaultdict(lambda: 100.0)
                days_off = (res.get("summary", {}) or {}).get("days_off_violations") or []
                if isinstance(days_off, dict):
                    for k, v in days_off.items():
                        try:
                            cnt = int(v)
                            rules_by_day[str(k)] = max(0.0, 100.0 - cnt * cfg["rules"]["days_off_violation_penalty"])
                        except Exception:
                            pass
                elif isinstance(days_off, list):
                    for it in days_off:
                        if isinstance(it, dict) and it.get("date"):
                            dkey = str(it["date"])
                            rules_by_day[dkey] = max(
                                0.0,
                                float(rules_by_day[dkey]) - float(cfg["rules"]["days_off_violation_penalty"])
                            )

                coverage_details = res.get("coverage_details") or {}
                if not isinstance(coverage_details, dict) or not coverage_details:
                    print("[HU1.2] coverage_details vacío; no se guardó quality por turno.")
                    inserted_quality = 0
                else:
                    insert_sql = f"""
                        INSERT INTO {quality_table}
                          ("Id","Token","DemandId","Date","WorkstationName","StartTime","EndTime",
                           "Demanded","Covered","Unmet",
                           "CoverageScore","FairnessScore","RulesScore","Score",
                           "Metrics","ConfigSnapshot","DateCreated")
                        VALUES
                          (%s,%s,%s::uuid,%s,%s,%s,%s,
                           %s,%s,%s,
                           %s,%s,%s,%s,
                           %s::jsonb,%s::jsonb,%s)
                    """

                    inserted_quality = 0

                    for demand_id, s in coverage_details.items():
                        if not isinstance(s, dict):
                            continue

                        d_str = s.get("date")
                        t_str = s.get("time")
                        if not d_str or not t_str or "-" not in t_str:
                            continue

                        day = datetime.fromisoformat(d_str).date()
                        hh1, hh2 = t_str.split("-", 1)

                        st = datetime.strptime(hh1.strip(), "%H:%M").time()
                        en = datetime.strptime(hh2.strip(), "%H:%M").time()

                        st_iv = timedelta(hours=st.hour, minutes=st.minute)
                        en_iv = timedelta(hours=en.hour, minutes=en.minute)

                        demanded = float(s.get("demanded") or 0.0)
                        covered = float(s.get("covered") or 0.0)
                        unmet = float(s.get("unmet") or max(0.0, demanded - covered))

                        cov_score = float(s.get("coverage_pct") or (100.0 if demanded == 0 else (covered / demanded) * 100.0))
                        cov_score = max(0.0, min(100.0, cov_score))

                        fair_score = float(fairness_by_day.get(day.isoformat(), 100.0))
                        rule_score = float(rules_by_day.get(day.isoformat(), 100.0))

                        score = (w_cov * cov_score) + (w_fair * fair_score) + (w_rule * rule_score)
                        score = round(max(0.0, min(100.0, score)), 2)

                        metrics = {
                            "date": day.isoformat(),
                            "time": t_str,
                            "weights": cfg["weights"],
                            "coverage_details_driven": True
                        }

                        cur.execute(
                            insert_sql,
                            (
                                uid(),
                                token,
                                str(demand_id),
                                day,
                                s.get("workstation"),
                                st_iv,
                                en_iv,
                                demanded,
                                covered,
                                unmet,
                                round(cov_score, 2),
                                round(fair_score, 2),
                                round(rule_score, 2),
                                score,
                                json.dumps(metrics, ensure_ascii=False),
                                json.dumps(cfg, ensure_ascii=False),
                                now(),
                            ),
                        )
                        inserted_quality += 1

                    print(f"[HU1.2][DB] inserted={inserted_quality} into {quality_table} token={token}")

                cur.execute("RELEASE SAVEPOINT hu12")
            except Exception as e:
                cur.execute("ROLLBACK TO SAVEPOINT hu12")
                cur.execute("RELEASE SAVEPOINT hu12")
                print("[HU1.2] Error (no aborta save):", str(e))
                import traceback
                traceback.print_exc()
                inserted_quality = 0

            # =========================================================
            # HU 1.3 - SUGERENCIAS DE MEJORA
            # Analiza gaps y scores para generar sugerencias accionables
            # Se guardan automáticamente en BD
            # =========================================================
            cur.execute("SAVEPOINT hu13")
            try:
                from services.sugerencias_mejora import SugerenciasMejoraService

                print(f"[HU1.3][SAVE] Generando sugerencias de mejora...")

                sug_svc = SugerenciasMejoraService(cur, debug=True)

                # Construir quality_result desde los datos disponibles
                quality_result = {
                    "score": 0,
                    "breakdown": {
                        "coverage": float(res.get("coverage_pct", 100) or 100),
                        "fairness": 100.0,
                        "rules": 100.0,
                    }
                }

                # Generar y guardar sugerencias (se guardan en BD automáticamente)
                sugerencias_generadas = sug_svc.generar_y_guardar(
                    gaps=explicaciones if explicaciones else [],
                    sched=sched,
                    emps=emps,
                    quality_result=quality_result,
                    token=token,
                    week_start=ws,
                    week_end=we,
                )

                print(f"[HU1.3][DB] inserted={len(sugerencias_generadas)} sugerencias token={token}")

                cur.execute("RELEASE SAVEPOINT hu13")

            except Exception as e:
                cur.execute("ROLLBACK TO SAVEPOINT hu13")
                cur.execute("RELEASE SAVEPOINT hu13")
                print("[HU1.3] Error (no aborta save):", str(e))
                import traceback
                traceback.print_exc()
                sugerencias_generadas = []

            # =========================================================
            # HU 1.4 - IA QUE APRENDE DEL HISTÓRICO (AUTO-TRAIN en SAVE)
            # - Sin endpoints extra
            # - 1) Carga modelo activo (AIModels)
            # - 2) Si no existe, entrena (BD; fallback CSV si existe en runtime)
            # - 3) Reajusta sched para cubrir gaps SIN violar reglas duras
            # - 4) Guarda ajustes en AIPredictions con el token de este save
            # =========================================================
            
            

            ajustes_ia = []  # evita NameError si no hay gaps o no hay modelo

            def _recalcular_cobertura_post_ia(res_dict, sched_dict):
                """Recalcula cobertura *desde cero* a partir del schedule (incluye ajustes IA).

                Usa res_dict["coverage_details"] como definición de slots demandados.
                Recalcula covered/unmet por slot contando asignaciones que solapan el intervalo
                y coinciden en workstation.
                """
                try:
                    details_before = res_dict.get("coverage_details") or {}
                    if not details_before:
                        return None

                    # Copia definición de slots y resetea cobertura
                    details_after = json.loads(json.dumps(details_before))
                    for _, slot in details_after.items():
                        demanded = float(slot.get("demanded") or 0.0)
                        slot["covered"] = 0.0
                        slot["unmet"] = float(max(0.0, demanded))
                        slot["coverage_pct"] = 0.0 if demanded > 0 else 100.0

                    def _parse_hhmm(s):
                        try:
                            h, m = (s or "00:00").split(":")
                            return int(h) * 60 + int(m)
                        except Exception:
                            return 0

                    # index: (date, ws_name) -> demand_ids
                    idx = {}
                    for did, slot in details_after.items():
                        d = slot.get("date")
                        ws = (slot.get("workstation") or "").strip().upper()
                        if not d or not ws:
                            continue
                        idx.setdefault((d, ws), []).append(did)

                    # Contar asignaciones por slot
                    for d, assigns in (sched_dict or {}).items():
                        d_iso = d.isoformat() if hasattr(d, "isoformat") else str(d)
                        for emp, dm in assigns:
                            if dm is None:
                                continue
                            ws_name = (getattr(dm, "wsname", "") or "").strip().upper()
                            if not ws_name:
                                continue

                            st = getattr(dm, "start", time(0, 0))
                            en = getattr(dm, "end", time(0, 0))
                            a_ini = st.hour * 60 + st.minute
                            a_fin = en.hour * 60 + en.minute
                            if a_fin <= a_ini:
                                a_fin += 24 * 60

                            for did in idx.get((d_iso, ws_name), []):
                                slot = details_after.get(did)
                                if not slot:
                                    continue
                                t = slot.get("time") or ""
                                if "-" not in t:
                                    continue
                                s1, s2 = t.split("-", 1)
                                s_ini = _parse_hhmm(s1)
                                s_fin = _parse_hhmm(s2)
                                if s_fin <= s_ini:
                                    s_fin += 24 * 60

                                if a_ini < s_fin and a_fin > s_ini:
                                    demanded = float(slot.get("demanded") or 0.0)
                                    covered = float(slot.get("covered") or 0.0)
                                    if covered < demanded:
                                        slot["covered"] = min(demanded, covered + 1.0)
                                        slot["unmet"] = float(max(0.0, demanded - slot["covered"]))
                                        slot["coverage_pct"] = (slot["covered"] / demanded * 100.0) if demanded > 0 else 100.0

                    total_demanded = sum(float(s.get("demanded") or 0.0) for s in details_after.values())
                    total_covered = sum(float(s.get("covered") or 0.0) for s in details_after.values())
                    pct_after = (total_covered / total_demanded * 100.0) if total_demanded > 0 else 100.0

                    # Guardar solo para respuesta
                    res_dict["coverage_details_after_ai"] = details_after
                    res_dict["summary"] = res_dict.get("summary") or {}
                    res_dict["summary"]["total_demanded_after_ai"] = float(total_demanded)
                    res_dict["summary"]["total_covered_after_ai"] = float(total_covered)
                    res_dict["summary"]["coverage_pct_after_ai"] = float(pct_after)
                    res_dict["summary"]["coverage_after_ai"] = f"{pct_after:.1f}%"
                    return pct_after
                except Exception as e:
                    print(f"[HU1.4][WARN] No pude recalcular cobertura post-IA: {e}")
                    return None
            cur.execute("SAVEPOINT hu14")

            ai_hu14_trained_pre = False
            ai_hu14_used_source_pre = None


            try:
                from services.aprendizaje_historico import AprendizajeHistoricoService
                import os

                print(f"[HU1.4][SAVE] Auto-train + reajuste (pre-DB insert) token={token}")

                ai_svc = AprendizajeHistoricoService(cur, debug=True)

                # 1) Intentar cargar modelo activo
                loaded = ai_svc._cargar_modelo_activo()

                # 2) Si no hay modelo activo: entrenar ahora mismo (para poder reajustar en este save)
                if not loaded:
                    # Ventana rolling: últimas 12 semanas hasta la semana actual
                    train_start = ws - timedelta(days=7 * 12)
                    train_end = we

                    try:
                        _stats = ai_svc.entrenar_desde_bd(train_start, train_end)
                        ai_hu14_trained_pre = True
                        ai_hu14_used_source_pre = "BD"
                        print(f"[HU1.4] Entrenado desde BD (pre): {_stats}")
                    except Exception as e_bd:
                        # Fallback a CSV local (solo si existe en ese runtime: local / lambda package)
                        csv_path = os.path.join(os.path.dirname(__file__), "_Schedules__202601300806.csv")
                        if os.path.exists(csv_path):
                            _stats = ai_svc.entrenar_desde_csv(csv_path)
                            ai_hu14_trained_pre = True
                            ai_hu14_used_source_pre = "CSV"
                            print(f"[HU1.4] Entrenado desde CSV (pre): {_stats}")
                        else:
                            print(f"[HU1.4][WARN] No pude entrenar ni desde BD ni CSV. Detalle BD: {e_bd}")
                            _stats = None

                # 3) Métricas de cobertura antes de IA (lo que venía del solver)
                coverage_pct_before_ai = float(
                    res.get("coverage_pct")
                    or (res.get("summary") or {}).get("coverage")
                    or 0.0
                )
                coverage_before_ai = res.get("coverage") or f"{coverage_pct_before_ai:.1f}%"

                # 4) Reajustar schedule para cubrir gaps (si hay modelo/reajustador)
                inserted_ai = 0
                if explicaciones:
                    sched_mejorado, ajustes_ia = ai_svc.reajustar_schedule(
                        sched=sched,
                        gaps=explicaciones,
                        emps=emps,
                        week=week,
                    )

                    if ajustes_ia:
                        sched = sched_mejorado  # <-- clave: esto es lo que termina guardándose en Schedules
                        inserted_ai = ai_svc.guardar_ajustes(ajustes_ia, token)
                        print(f"[HU1.4][DB] ajustes_aplicados={len(ajustes_ia)}; inserted={inserted_ai} en AIPredictions token={token}")
                    else:
                        print("[HU1.4] No se aplicaron ajustes (no hay candidatos válidos sin romper reglas).")
                else:
                    print("[HU1.4] No hay gaps -> no se intenta reajuste.")
                    ajustes_ia = []

                # 5) ✅ Recalcular cobertura con el schedule FINAL (incluye IA si hubo)
                pct_after = _recalcular_cobertura_post_ia(res, sched)
                if pct_after is not None and pct_after > coverage_pct_before_ai:
                    res["coverage_pct"] = float(pct_after)
                    res["coverage"] = f"{pct_after:.1f}%"
                elif pct_after is not None:
                    # La IA no mejoró, conservar cobertura original
                    print(f"[HU1.4][INFO] Cobertura post-IA ({pct_after:.1f}%) <= pre-IA ({coverage_pct_before_ai:.1f}%). Conservando schedule con ajustes IA pero reportando cobertura real.")
                    res["coverage_pct"] = float(pct_after)
                    res["coverage"] = f"{pct_after:.1f}%"

                res["summary"] = res.get("summary") or {}
                res["summary"]["coverage_before_ai"] = coverage_before_ai
                res["summary"]["coverage_after_ai"] = res.get("coverage") or coverage_before_ai
                res["summary"]["coverage_pct_before_ai"] = float(coverage_pct_before_ai or 0.0)
                res["summary"]["coverage_pct_after_ai"] = float(res.get("coverage_pct") or 0.0)
                res["summary"]["hu14_ai_adjustments"] = int(len(ajustes_ia or []))
                res["summary"]["hu14_ai_rows_inserted"] = int(inserted_ai or 0)

                cur.execute("RELEASE SAVEPOINT hu14")
            except Exception as e:
                cur.execute("ROLLBACK TO SAVEPOINT hu14")
                cur.execute("RELEASE SAVEPOINT hu14")
                print("[HU1.4] Error (no aborta save):", str(e))
                import traceback
                traceback.print_exc()
                ajustes_ia = []

            # =========================================================
            # GUARDAR SCHEDULES EN BD
            # (Tu lógica existente de overrides + coalesce + inserts)
            # =========================================================
            overrides_list = (
                (res.get("summary", {}) or {})
                .get("usershift_free_overrides", [])
                or []
            )
            overrides_set = {
                (str(o.get("employee_id")), datetime.fromisoformat(o.get("date")).date())
                for o in overrides_list
                if o.get("employee_id") and o.get("date")
            }

            latest_map_all_by_wsid = res.get("latest_end_by_wsid", {}) or {}
            latest_map_all_by_day = res.get("latest_end_of_day", {}) or {}

            for d in sorted(sched.keys()):
                ass = sorted(
                    sched[d],
                    key=lambda x: (
                        x[0].name,
                        x[1].wsname if x[1] else "",
                        _t2m(x[1].start) if x[1] else 0,
                    ),
                )

                # Ausencias
                for emp, dm in ass:
                    if dm is None or dm.wsid is None:
                        cur.execute(
                            '''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation",
                                 "IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                            ''',
                            (
                                uid(),
                                d,
                                str(emp.id),
                                None,
                                None,
                                None,
                                emp.abs_reason.get(d, 'ABS') if hasattr(emp, 'abs_reason') else 'ABS',
                                False,
                                now(),
                            ),
                        )

                # Coalesce + obs
                coalesced = coalesce_employee_day_workstation(ass)

                # --- FILTRO (ajustado): NO eliminar segmentos cortos por workstation en flexible mode.
                # Un empleado puede alternar estaciones dentro de un mismo turno. La regla "mínimo 3h" aplica al
                # total del día (o bloque continuo), no a cada segmento por estación.
                from collections import defaultdict

                MIN_BLOCK_SAVE_MIN = int(MIN_SHIFT_DURATION_HOURS * 60)

                # total minutos por empleado en el día d (sumando todas las estaciones)
                _total_min_by_eid = defaultdict(int)
                for (eid_filt, wsid_filt), rows_filt in coalesced.items():
                    if wsid_filt is None:
                        continue
                    for emp_f, s_min_f, e_min_f, src_dms_f in rows_filt:
                        dur_min_f = max(0, int(e_min_f - s_min_f))
                        _total_min_by_eid[eid_filt] += dur_min_f

                # Si el total del día < mínimo, se omite TODO el día para ese empleado; si no, se guardan todos los segmentos (aunque sean cortos).
                _logged_min_day = set()
                for (eid_filt, wsid_filt), rows_filt in list(coalesced.items()):
                    if wsid_filt is None:
                        continue
                    day_total = _total_min_by_eid.get(eid_filt, 0)
                    if day_total < MIN_BLOCK_SAVE_MIN:
                        if ASCII_LOGS and eid_filt not in _logged_min_day:
                            any_name = rows_filt[0][0].name if rows_filt else str(eid_filt)
                            print(f"[SAVE-MIN-DAY] Día {d} omitido para {any_name} ({eid_filt}): total {day_total/60:.2f}h < {MIN_SHIFT_DURATION_HOURS}h")
                            _logged_min_day.add(eid_filt)
                        coalesced[(eid_filt, wsid_filt)] = []
                    else:
                        # limpiar solo segmentos inválidos (0 o negativos)
                        filtered_rows = []
                        for emp_f, s_min_f, e_min_f, src_dms_f in rows_filt:
                            if e_min_f > s_min_f:
                                filtered_rows.append((emp_f, s_min_f, e_min_f, src_dms_f))
                        coalesced[(eid_filt, wsid_filt)] = filtered_rows
                # --- FIN FILTRO ---


                # --- CAP de 10h/día por empleado (sin duplicar híbridos) ---
                DAILY_CAP_MIN = MAX_HOURS_PER_DAY * 60

                real_minutes_by_emp = {}
                for (eid0, wsid0), _rows0 in coalesced.items():
                    if eid0 not in real_minutes_by_emp:
                        real_minutes_by_emp[eid0] = []
                    for emp0, s0, e0, src0 in _rows0:
                        real_minutes_by_emp[eid0].append((s0, e0, wsid0))

                actual_worked_minutes = {}
                for eid, intervals in real_minutes_by_emp.items():
                    if not intervals:
                        actual_worked_minutes[eid] = 0
                        continue
                    sorted_ivs = sorted(intervals, key=lambda x: (x[0], x[1]))
                    merged = [[sorted_ivs[0][0], sorted_ivs[0][1]]]
                    for s, e, _ in sorted_ivs[1:]:
                        if s <= merged[-1][1]:
                            merged[-1][1] = max(merged[-1][1], e)
                        else:
                            merged.append([s, e])
                    actual_worked_minutes[eid] = sum(e - s for s, e in merged)

                remaining_quota = {eid: DAILY_CAP_MIN for eid in real_minutes_by_emp.keys()}

                for (eid0, wsid0), _rows0 in list(coalesced.items()):
                    new_rows = []
                    for emp0, s0, e0, src0 in _rows0:
                        if actual_worked_minutes.get(eid0, 0) <= DAILY_CAP_MIN:
                            new_rows.append((emp0, s0, e0, src0))
                        else:
                            quota = remaining_quota.get(eid0, DAILY_CAP_MIN)
                            if quota <= 0:
                                continue
                            seg = e0 - s0
                            use = seg if seg <= quota else quota
                            ns, ne = s0, s0 + use
                            remaining_quota[eid0] = quota - use
                            if (ne - ns) >= MIN_SEGMENT_MINUTES:
                                if ASCII_LOGS and use < seg:
                                    print(
                                        f"[SAVE-CAP10H] Recorte {emp0.name} {d} ws={wsid0}: "
                                        f"{_m2t(s0).strftime('%H:%M')}-{_m2t(e0 if e0 < 24*60 else 0).strftime('%H:%M')}"
                                        f" → {_m2t(ns).strftime('%H:%M')}-{_m2t(ne if ne < 24*60 else 0).strftime('%H:%M')}"
                                    )
                                new_rows.append((emp0, ns, ne, src0))
                    coalesced[(eid0, wsid0)] = new_rows
                # --- fin CAP 10h ---

                day_key = d.isoformat()
                latest_end_by_wsid_min = latest_map_all_by_wsid.get(day_key, {}) or {}
                latest_end_of_day_min = latest_map_all_by_day.get(day_key, None)

                for (eid, wsid), rows in coalesced.items():
                    if wsid is None:
                        continue

                    for emp, s_min, e_min, src_dms in rows:
                        s_t = _m2t(s_min)
                        e_t = _m2t(e_min if e_min < 24 * 60 else 0)
                        dur_min = e_min - s_min
                        if dur_min < MIN_SEGMENT_MINUTES:
                            if ASCII_LOGS:
                                print(
                                    f"[SAVE-GUARD] Segmento <{MIN_SEGMENT_MINUTES}m omitido: "
                                    f"user={emp.name}, fecha={d}, wsid={wsid}, "
                                    f"{s_t.strftime('%H:%M')}-{e_t.strftime('%H:%M')}"
                                )
                            continue

                        has_fixed = any((emp.id, dm.id) in fixed_ids for dm in src_dms)
                        if has_fixed:
                            obs = ""
                        else:
                            enforced_us = (str(emp.id), d) not in overrides_set

                            last_wsid_end = latest_end_by_wsid_min.get(str(wsid))
                            last_day_end = latest_end_of_day_min

                            if enforced_us and (
                                (last_wsid_end is not None and e_min == last_wsid_end)
                                or (last_day_end is not None and e_min == last_day_end)
                            ):
                                obs = ""
                            elif last_wsid_end is not None and e_min == last_wsid_end:
                                obs = "C"
                            else:
                                obs = "BT"

                        cur.execute(
                            '''
                            INSERT INTO "Management"."Schedules"
                                ("Id","Date","UserId","WorkstationId",
                                 "StartTime","EndTime","Observation",
                                 "IsDeleted","DateCreated")
                            VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                            ''',
                            (
                                uid(),
                                d,
                                str(emp.id),
                                str(wsid),
                                timedelta(hours=s_t.hour, minutes=s_t.minute),
                                timedelta(hours=e_t.hour, minutes=e_t.minute),
                                obs,
                                False,
                                now(),
                            ),
                        )

            # =========================================================
            # HU 1.4 - Entrenamiento continuo POST-GUARDADO
            # (para que el modelo aprenda de la semana recién insertada en Schedules)
            # =========================================================
            cur.execute("SAVEPOINT hu14_post")
            try:
                from services.aprendizaje_historico import AprendizajeHistoricoService

                ai_svc_post = AprendizajeHistoricoService(cur, debug=True)

                # Re-entrenar con ventana rolling incluyendo la semana recién guardada
                train_start = ws - timedelta(days=7 * 12)
                train_end = we

                stats_post = ai_svc_post.entrenar_desde_bd(train_start, train_end)

                # Guardar modelo como activo (AIModels)
                model_id = ai_svc_post.guardar_modelo(nombre="auto", version=f"auto-{ws.isoformat()}")

                # Registrar corrida en AITrainingHistory (no bloquea si falla)
                try:
                    ai_svc_post.registrar_training_history(
                        model_id=model_id,
                        data_start=train_start,
                        data_end=train_end,
                        notes=f"post-save token={token} ajustes={len(ajustes_ia)}",
                        coverage_improvement=float((res.get("summary", {}) or {}).get("coverage_pct_after_ai", 0.0) - float((res.get("summary", {}) or {}).get("coverage_pct_before_ai", 0.0))),
                    )
                except Exception as _e:
                    print(f"[HU1.4][DB] AITrainingHistory skip (ok): {_e}")

                print(f"[HU1.4][POST] Modelo guardado activo id={model_id} stats={stats_post}")

                cur.execute("RELEASE SAVEPOINT hu14_post")
            except Exception as e:
                cur.execute("ROLLBACK TO SAVEPOINT hu14_post")
                cur.execute("RELEASE SAVEPOINT hu14_post")
                print("[HU1.4][POST] Error (no aborta save):", str(e))
                import traceback
                traceback.print_exc()


            cleanup_null_workstation_schedules(cur, ws, we)
            c.commit()

    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({"error": "Error al guardar", "detail": str(e)}), 500

    # =========================================================
    # RESPUESTA + RESUMEN DE TODAS LAS HUs
    # =========================================================
    out = dict(res) if isinstance(res, dict) else {"result": res}
    out.setdefault("summary", {})
    out["summary"]["token"] = token
    out["summary"]["hu11_gaps_inserted"] = inserted_gaps
    out["summary"]["hu12_quality_rows_inserted"] = inserted_quality
    out["summary"]["hu13_suggestions_generated"] = len(sugerencias_generadas) if sugerencias_generadas else 0
    out["summary"]["hu14_ai_adjustments"] = len(ajustes_ia) if ajustes_ia else 0

    return jsonify(
        {
            "message": ("Horario guardado (flexible)" if flexible else "Horario guardado"),
            **out,
        }
    ), 201


# ───────── MAIN ─────────
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
if __name__ == "__main__":
    print("API Gandarias v3.14 en http://localhost:5000")
    print("Modo flexible nunca responde 'sin solución': usa fallback greedy si hace falta.")
    app.run(host="0.0.0.0", port=5000, debug=True)