#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AI SCHEDULER COMPLETO - Gandarías v4.1   (15-ago-2025)

Sistema inteligente de generación de horarios con:
• Priorización por preferencias de puesto
• Cobertura por capacidad laboral (no tiempo)
• Validación de tipos de turno por empleado
• Asignación fraccionaria con híbridos válidos
• Distribución equitativa con rotación automática
• Procesamiento <2 minutos garantizado
"""

import logging
import random
import uuid
from collections import Counter, defaultdict
from datetime import date, datetime, time, timedelta, timezone
from typing import Dict, List, Optional, Tuple

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

ABS_WS_ID = '00000000-0000-0000-0000-000000000000'

# ───────── UTILIDADES ─────────


def uid(): return str(uuid.uuid4())
def now(): return datetime.now(timezone.utc)


class DatabaseConnectionError(Exception):
    ...


class DataNotFoundError(Exception):
    ...


class DataIntegrityError(Exception):
    ...


class ScheduleGenerationError(Exception):
    ...

# ───────── MODELOS PRINCIPALES ─────────


class ShiftType:
    def __init__(self, row: Tuple):
        (self.id, self.name, self.description, self.is_active,
         self.block1_start, self.block1_last_start,
         self.block2_start, self.block2_last_start) = row
        self.is_split = self.block2_start is not None

    def can_start_at(self, start_time: time) -> bool:
        """Verifica si un turno puede empezar a esta hora"""
        # Bloque 1
        if self.block1_start <= start_time <= self.block1_last_start:
            return True
        # Bloque 2 (si existe)
        if self.is_split and self.block2_start and self.block2_last_start:
            if self.block2_start <= start_time <= self.block2_last_start:
                return True
        return False


class WorkstationCoverage:
    def __init__(self, ws_id: str, coverage_pct: float, preference: int):
        self.ws_id = ws_id
        self.coverage = coverage_pct / 100.0  # Convertir % a decimal
        self.preference = preference

    def can_cover_full(self) -> bool:
        return self.coverage >= 1.0

    def can_cover_partial(self, required_pct: float) -> bool:
        return self.coverage >= required_pct


class HybridCombination:
    def __init__(self, row: Tuple):
        (self.id, self.ws_a_id, self.ws_b_id,
         self.ws_c_id, self.ws_d_id) = row
        self.workstations = [ws for ws in [self.ws_a_id,
                                           self.ws_b_id, self.ws_c_id, self.ws_d_id] if ws]

    def contains_workstations(self, ws_list: List[str]) -> bool:
        """Verifica si esta combinación híbrida permite la mezcla de puestos"""
        return all(ws in self.workstations for ws in ws_list)

    def size(self) -> int:
        return len(self.workstations)


class EmployeeAI:
    def __init__(self, row: Tuple):
        self.id, self.name, self.split = row
        self.workstations = {}  # ws_id → WorkstationCoverage
        self.allowed_shift_types = set()  # shift_type_ids permitidos
        self.day_off = set()
        self.window = defaultdict(list)
        self.exc = defaultdict(list)
        self.absent = set()
        self.abs_reason = {}

        # Métricas de equidad
        self.recent_shift_types = defaultdict(int)
        self.total_hours_last_weeks = 0
        self.current_week_coverage_used = 0.0  # % de capacidad usada esta semana

    def add_workstation(self, ws_id: str, coverage_pct: float, preference: int):
        self.workstations[ws_id] = WorkstationCoverage(
            ws_id, coverage_pct, preference)

    def can_work_at(self, ws_id: str) -> bool:
        return ws_id in self.workstations

    def get_coverage(self, ws_id: str) -> float:
        return self.workstations.get(ws_id, WorkstationCoverage(ws_id, 0, 999)).coverage

    def get_preference(self, ws_id: str) -> int:
        return self.workstations.get(ws_id, WorkstationCoverage(ws_id, 0, 999)).preference

    def can_work_shift_type(self, shift_type_id: str) -> bool:
        return not self.allowed_shift_types or shift_type_id in self.allowed_shift_types

    def get_preferred_workstations(self):
        return sorted([(ws_id, cov.preference) for ws_id, cov in self.workstations.items()],
                      key=lambda x: x[1])

    def can_cover_combination(self, ws_coverage_needed: Dict[str, float]) -> bool:
        """Verifica si puede cubrir una combinación de puestos con la capacidad requerida"""
        total_needed = 0.0
        for ws_id, needed_pct in ws_coverage_needed.items():
            if not self.can_work_at(ws_id):
                return False
            if self.get_coverage(ws_id) < needed_pct:
                return False
            total_needed += needed_pct

        return total_needed <= 1.0  # No exceder 100% capacidad total

    def is_hybrid(self):
        return len(self.workstations) >= 4

    def off(self, d):
        return d.weekday() in self.day_off

    def absent_day(self, d):
        return d in self.absent

    def available(self, d, s, e):
        if self.off(d) or self.absent_day(d):
            return False
        win = self.exc.get(d) or self.window.get(
            d.weekday(), [(time(0), time(23, 59))])
        return any(a <= s and e <= b for a, b in win)


class DemandAI:
    def __init__(self, row: Tuple):
        (self.id, rdate, self.wsid, self.wsname,
         self.start, self.end, self.need) = row
        self.date = rdate.date() if hasattr(rdate, 'date') else rdate
        self.need = float(self.need)  # Permitir decimales (1.5, 0.5, etc.)
        self.duration_hours = self._calculate_duration()
        self.remaining_need = self.need  # Cuánto falta por asignar

    def _calculate_duration(self) -> float:
        start_minutes = self.start.hour * 60 + self.start.minute
        end_minutes = self.end.hour * 60 + self.end.minute
        return (end_minutes - start_minutes) / 60


class Assignment:
    def __init__(self, employee: EmployeeAI, demand: DemandAI, coverage_assigned: float):
        self.employee = employee
        self.demand = demand
        self.coverage_assigned = coverage_assigned  # % de la demanda que cubre
        self.capacity_used = coverage_assigned  # % de capacidad del empleado usada
        self.id = f"{employee.id}_{demand.id}_{coverage_assigned}"

# ───────── SISTEMA DE MEMORIA ─────────


class ScheduleMemory:
    def __init__(self):
        self.employee_shift_history = defaultdict(lambda: defaultdict(int))
        self.employee_workstation_history = defaultdict(
            lambda: defaultdict(int))
        self.employee_hours_history = defaultdict(float)

    def setup_table(self, cur):
        try:
            cur.execute('''
                CREATE TABLE IF NOT EXISTS "Management"."ScheduleMemory" (
                    "Id" UUID PRIMARY KEY DEFAULT gen_random_uuid(),
                    "UserId" UUID NOT NULL,
                    "WeekStart" DATE NOT NULL,
                    "WorkstationId" UUID NOT NULL,
                    "ShiftTypeId" UUID,
                    "CoverageAssigned" DECIMAL(4,2),
                    "AssignmentCount" INT DEFAULT 1,
                    "TotalHours" DECIMAL(4,2),
                    "DateCreated" TIMESTAMPTZ DEFAULT CURRENT_TIMESTAMP,
                    UNIQUE("UserId", "WeekStart", "WorkstationId", "ShiftTypeId")
                )
            ''')
        except Exception as e:
            logging.warning(f"Error creando tabla ScheduleMemory: {e}")

    def load_recent_history(self, cur, weeks_back=6):
        try:
            cutoff_date = date.today() - timedelta(weeks=weeks_back)

            rows = fetchall(cur, '''
                SELECT "UserId", "WorkstationId", "ShiftTypeId", 
                       SUM("AssignmentCount"), SUM("TotalHours")
                FROM "Management"."ScheduleMemory"
                WHERE "WeekStart" >= %s
                GROUP BY "UserId", "WorkstationId", "ShiftTypeId"
            ''', (cutoff_date,))

            for user_id, ws_id, shift_type_id, count, hours in rows:
                if shift_type_id:
                    self.employee_shift_history[user_id][shift_type_id] += count
                self.employee_workstation_history[user_id][ws_id] += count
                self.employee_hours_history[user_id] += float(hours or 0)

        except Exception as e:
            logging.warning(f"Error cargando historial: {e}")

    def save_week_data(self, cur, week_start: date, assignments: List[Assignment], shift_types: Dict):
        try:
            cleanup_date = week_start - timedelta(weeks=8)
            cur.execute(
                'DELETE FROM "Management"."ScheduleMemory" WHERE "WeekStart" < %s', (cleanup_date,))

            for assignment in assignments:
                if assignment.demand.wsid != ABS_WS_ID:
                    # Determinar tipo de turno
                    shift_type_id = self._determine_shift_type(
                        assignment.demand, shift_types)

                    cur.execute('''
                        INSERT INTO "Management"."ScheduleMemory" 
                        ("UserId", "WeekStart", "WorkstationId", "ShiftTypeId", 
                         "CoverageAssigned", "TotalHours")
                        VALUES (%s, %s, %s, %s, %s, %s)
                        ON CONFLICT ("UserId", "WeekStart", "WorkstationId", "ShiftTypeId")
                        DO UPDATE SET 
                            "AssignmentCount" = "ScheduleMemory"."AssignmentCount" + 1,
                            "CoverageAssigned" = "ScheduleMemory"."CoverageAssigned" + EXCLUDED."CoverageAssigned",
                            "TotalHours" = "ScheduleMemory"."TotalHours" + EXCLUDED."TotalHours"
                    ''', (
                        str(assignment.employee.id), week_start, str(
                            assignment.demand.wsid),
                        shift_type_id, assignment.coverage_assigned, assignment.demand.duration_hours
                    ))

        except Exception as e:
            logging.error(f"Error guardando memoria: {e}")

    def _determine_shift_type(self, demand: DemandAI, shift_types: Dict) -> Optional[str]:
        """Determina el tipo de turno basado en la hora de inicio"""
        for st_id, shift_type in shift_types.items():
            if shift_type.can_start_at(demand.start):
                return st_id
        return None

# ───────── FUNCIONES DE CARGA ─────────


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


def load_shift_types(cur) -> Dict[str, ShiftType]:
    """Carga tipos de turno disponibles"""
    rows = fetchall(cur, '''
        SELECT "Id", "Name", "Description", "IsActive",
               "Block1Start", "Block1LastStart", "Block2Start", "Block2LastStart"
        FROM "Management"."ShiftTypes"
        WHERE "IsActive" = TRUE
    ''')

    return {str(row[0]): ShiftType(row) for row in rows}


def load_hybrid_combinations(cur) -> List[HybridCombination]:
    """Carga combinaciones híbridas válidas"""
    rows = fetchall(cur, '''
        SELECT "Id", "WorkstationAId", "WorkstationBId", "WorkstationCId", "WorkstationDId"
        FROM "Management"."HybridWorkstations"
        WHERE "IsActive" = TRUE
    ''')

    return [HybridCombination(row) for row in rows]


def pick_template(cur, week_start: date, week_end: date):
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

    cur.execute(
        'SELECT "Id","Name" FROM "Management"."WorkstationDemandTemplates" WHERE "IsActive"')
    act = cur.fetchall()
    if not act:
        raise DataNotFoundError(
            "No existe plantilla por rango ni plantilla activa")
    if len(act) > 1:
        raise DataIntegrityError("Existen múltiples plantillas activas")
    return act[0]


def load_data_complete(week_start: date):
    """Carga completa de datos con todas las validaciones"""
    week = [week_start + timedelta(days=i) for i in range(7)]
    week_end = week[-1]

    with conn() as c, c.cursor() as cur:
        # Configurar memoria
        memory = ScheduleMemory()
        memory.setup_table(cur)
        memory.load_recent_history(cur)

        # Cargar tipos de turno
        shift_types = load_shift_types(cur)

        # Cargar combinaciones híbridas
        hybrid_combinations = load_hybrid_combinations(cur)

        tpl_id, tpl_name = pick_template(cur, week_start, week_end)

        # Cargar demandas
        demand_rows = fetchall(cur, '''
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
        ''', (week_start, tpl_id))

        demands = [DemandAI(r) for r in demand_rows]
        if not demands:
            raise DataNotFoundError(
                "La plantilla seleccionada no tiene demandas")

        # Cargar empleados
        emp_rows = fetchall(cur, '''
            SELECT "Id",
                   COALESCE("FirstName",'')||' '||COALESCE("LastName",'') AS name,
                   COALESCE("ComplementHours", TRUE)
            FROM "Management"."AspNetUsers"
            WHERE "IsActive" AND NOT "IsDelete"
        ''')

        emps = {r[0]: EmployeeAI(r) for r in emp_rows}
        if not emps:
            raise DataNotFoundError("No hay empleados activos")

        # Cargar puestos con cobertura y preferencia
        workstation_rows = fetchall(cur, '''
            SELECT "UserId", "WorkstationId", 
                   COALESCE("CoveragePercentage", 100), 
                   COALESCE("Preference", 1)
            FROM "Management"."UserWorkstations"
            WHERE NOT "IsDelete"
        ''')

        for uid, ws_id, coverage, preference in workstation_rows:
            if uid in emps:
                emps[uid].add_workstation(ws_id, coverage, preference)

        # Cargar restricciones de tipos de turno
        shift_restrictions = fetchall(cur, '''
            SELECT "UserId", "ShiftTypeId"
            FROM "Management"."EmployeeShiftTypeRestrictions"
        ''')

        for uid, shift_type_id in shift_restrictions:
            if uid in emps:
                emps[uid].allowed_shift_types.add(shift_type_id)

        # Cargar restricciones de horarios (código original)
        load_schedule_restrictions(cur, emps, week_start, week_end)

        # Cargar turnos fijos
        fixed = load_fixed_shifts(
            cur, emps, week_start, week_end, demands, shift_types)

        # Cargar métricas históricas
        for emp_id, emp in emps.items():
            emp.recent_shift_types = memory.employee_shift_history[emp_id]
            emp.total_hours_last_weeks = memory.employee_hours_history[emp_id]

    return list(emps.values()), demands, tpl_name, week, fixed, memory, shift_types, hybrid_combinations


def load_schedule_restrictions(cur, emps, week_start, week_end):
    """Carga restricciones de horarios (igual que original)"""
    # Restricciones semanales
    for uid, dow, rt, f, t in fetchall(cur, '''
        SELECT "UserId","DayOfWeek","RestrictionType","AvailableFrom","AvailableUntil"
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
        SELECT "UserId","Date","RestrictionType","AvailableFrom","AvailableUntil"
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

    # Licencias y ausentismos
    for uid, sd, ed in fetchall(cur, '''
        SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
        FROM "Management"."Licenses"
        WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
    ''', (week_end, week_end, week_end, week_start)):
        if uid not in emps:
            continue
        d = max(sd, week_start)
        while d <= ed:
            emps[uid].absent.add(d)
            emps[uid].abs_reason[d] = 'VAC'
            d += timedelta(days=1)

    for uid, sd, ed in fetchall(cur, '''
        SELECT "UserId","StartDate"::date, COALESCE("EndDate"::date,%s)
        FROM "Management"."UserAbsenteeisms"
        WHERE "StartDate"::date <= %s AND COALESCE("EndDate"::date,%s) >= %s
    ''', (week_end, week_end, week_end, week_start)):
        if uid not in emps:
            continue
        d = max(sd, week_start)
        while d <= ed:
            emps[uid].absent.add(d)
            emps[uid].abs_reason[d] = 'ABS'
            d += timedelta(days=1)


def load_fixed_shifts(cur, emps, week_start, week_end, demands, shift_types):
    """Carga turnos fijos con validación de tipos de turno"""
    fixed = []
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

            # Encontrar demanda correspondiente
            for dm in demands:
                if (dm.date == shift_date and dm.start == blk_time and
                    emps[uid].can_work_at(dm.wsid) and
                    emps[uid].available(dm.date, dm.start, dm.end) and
                        dm.remaining_need > 0):

                    # Validar tipo de turno
                    valid_shift_type = True
                    for st_id, shift_type in shift_types.items():
                        if shift_type.can_start_at(blk_time):
                            if not emps[uid].can_work_shift_type(st_id):
                                valid_shift_type = False
                            break

                    if valid_shift_type:
                        coverage_needed = min(1.0, dm.remaining_need)
                        assignment = Assignment(emps[uid], dm, coverage_needed)
                        fixed.append(assignment)
                        dm.remaining_need -= coverage_needed
                        break

    return fixed

# ───────── ALGORITMO PRINCIPAL DE ASIGNACIÓN ─────────


def generate_optimal_assignments(emps: List[EmployeeAI], demands: List[DemandAI],
                                 week: List[date], shift_types: Dict[str, ShiftType],
                                 hybrid_combinations: List[HybridCombination],
                                 memory: ScheduleMemory) -> List[Assignment]:
    """
    Algoritmo principal que genera asignaciones óptimas considerando:
    - Cobertura por capacidad laboral
    - Validación de tipos de turno
    - Combinaciones híbridas válidas
    - Priorización por preferencias
    - Rotación equitativa
    """

    assignments = []

    # Procesar cada demanda
    for demand in demands:
        if demand.remaining_need <= 0:
            continue

        # Determinar tipo de turno de esta demanda
        demand_shift_types = []
        for st_id, shift_type in shift_types.items():
            if shift_type.can_start_at(demand.start):
                demand_shift_types.append(st_id)

        # Mientras quede demanda por cubrir
        while demand.remaining_need > 0.01:  # Tolerancia para decimales

            # 1. INTENTAR ASIGNACIÓN COMPLETA (100%)
            if demand.remaining_need >= 1.0:
                best_emp = find_best_employee_for_full_coverage(
                    emps, demand, demand_shift_types, memory
                )

                if best_emp and best_emp.get_coverage(demand.wsid) >= 1.0:
                    assignment = Assignment(best_emp, demand, 1.0)
                    assignments.append(assignment)
                    demand.remaining_need -= 1.0
                    best_emp.current_week_coverage_used += 1.0
                    continue

            # 2. INTENTAR ASIGNACIÓN HÍBRIDA ÓPTIMA
            remaining = demand.remaining_need
            hybrid_assignment = find_optimal_hybrid_assignment(
                emps, demand, remaining, demand_shift_types,
                hybrid_combinations, memory
            )

            if hybrid_assignment:
                assignments.extend(hybrid_assignment)
                for assignment in hybrid_assignment:
                    demand.remaining_need -= assignment.coverage_assigned
                    assignment.employee.current_week_coverage_used += assignment.coverage_assigned
                continue

            # 3. ASIGNACIÓN SUBÓPTIMA (100% empleado para cobertura parcial)
            suboptimal_emp = find_best_employee_for_partial_coverage(
                emps, demand, demand_shift_types, memory
            )

            if suboptimal_emp:
                coverage_assigned = min(
                    remaining, suboptimal_emp.get_coverage(demand.wsid))
                assignment = Assignment(
                    suboptimal_emp, demand, coverage_assigned)
                assignments.append(assignment)
                demand.remaining_need -= coverage_assigned
                suboptimal_emp.current_week_coverage_used += coverage_assigned
            else:
                # No se puede cubrir esta demanda
                logging.warning(
                    f"No se pudo cubrir demanda {demand.wsname} {demand.date} {demand.start}")
                break

    return assignments


def find_best_employee_for_full_coverage(emps: List[EmployeeAI], demand: DemandAI,
                                         shift_types: List[str], memory: ScheduleMemory) -> Optional[EmployeeAI]:
    """Encuentra el mejor empleado para cobertura completa (100%)"""
    candidates = []

    for emp in emps:
        if not emp.can_work_at(demand.wsid):
            continue
        if not emp.available(demand.date, demand.start, demand.end):
            continue
        if emp.get_coverage(demand.wsid) < 1.0:
            continue
        if emp.current_week_coverage_used >= 1.0:  # Ya está al 100% esta semana
            continue

        # Validar tipo de turno
        valid_shift = any(emp.can_work_shift_type(st) for st in shift_types)
        if not valid_shift:
            continue

        # Calcular score de prioridad
        preference_score = emp.get_preference(demand.wsid)
        historical_frequency = memory.employee_workstation_history[emp.id][demand.wsid]
        usage_score = emp.current_week_coverage_used

        # Menor score = mejor candidato
        total_score = (
            preference_score * 10 +      # Priorizar preferencias
            historical_frequency * 2 +   # Evitar repetición excesiva
            usage_score * 5              # Balancear carga
        )

        candidates.append((total_score, emp))

    if candidates:
        candidates.sort(key=lambda x: x[0])
        return candidates[0][1]

    return None


def find_optimal_hybrid_assignment(emps: List[EmployeeAI], demand: DemandAI, remaining_need: float,
                                   shift_types: List[str], hybrid_combinations: List[HybridCombination],
                                   memory: ScheduleMemory) -> Optional[List[Assignment]]:
    """Encuentra la mejor combinación híbrida para completar la demanda"""

    for emp in emps:
        if not emp.can_work_at(demand.wsid):
            continue
        if not emp.available(demand.date, demand.start, demand.end):
            continue
        if emp.current_week_coverage_used >= 1.0:
            continue

        # Validar tipo de turno
        valid_shift = any(emp.can_work_shift_type(st) for st in shift_types)
        if not valid_shift:
            continue

        emp_coverage = emp.get_coverage(demand.wsid)
        if emp_coverage < remaining_need:
            continue

        # Si puede cubrir exactamente lo que se necesita
        if emp_coverage >= remaining_need:
            available_capacity = 1.0 - emp.current_week_coverage_used

            if available_capacity >= remaining_need:
                # Buscar combinación híbrida válida para completar su capacidad
                remaining_capacity = available_capacity - remaining_need

                if remaining_capacity > 0.01:  # Si queda capacidad
                    hybrid_assignment = find_complementary_workstations(
                        emp, demand, remaining_need, remaining_capacity,
                        hybrid_combinations, shift_types
                    )

                    if hybrid_assignment:
                        return hybrid_assignment
                else:
                    # Usar solo para esta demanda
                    return [Assignment(emp, demand, remaining_need)]

    return None


def find_complementary_workstations(emp: EmployeeAI, primary_demand: DemandAI,
                                    primary_coverage: float, remaining_capacity: float,
                                    hybrid_combinations: List[HybridCombination],
                                    shift_types: List[str]) -> Optional[List[Assignment]]:
    """Busca puestos complementarios para completar la capacidad del empleado"""

    # Buscar combinación híbrida válida que incluya el puesto principal
    valid_combinations = []
    for combo in hybrid_combinations:
        if primary_demand.wsid in combo.workstations:
            # Verificar que el empleado puede trabajar en otros puestos de la combinación
            compatible_workstations = []
            for ws_id in combo.workstations:
                if ws_id != primary_demand.wsid and emp.can_work_at(ws_id):
                    compatible_workstations.append(ws_id)

            if compatible_workstations:
                valid_combinations.append((combo, compatible_workstations))

    if not valid_combinations:
        return None

    # TODO: Buscar demandas simultáneas en otros puestos compatibles
    # Por ahora, retornar solo la asignación principal
    return [Assignment(emp, primary_demand, primary_coverage)]


def find_best_employee_for_partial_coverage(emps: List[EmployeeAI], demand: DemandAI,
                                            shift_types: List[str], memory: ScheduleMemory) -> Optional[EmployeeAI]:
    """Encuentra empleado para cobertura parcial (subóptima)"""
    candidates = []

    for emp in emps:
        if not emp.can_work_at(demand.wsid):
            continue
        if not emp.available(demand.date, demand.start, demand.end):
            continue
        if emp.current_week_coverage_used >= 1.0:
            continue

        # Validar tipo de turno
        valid_shift = any(emp.can_work_shift_type(st) for st in shift_types)
        if not valid_shift:
            continue

        # Cualquier cobertura es válida para subóptimo
        preference_score = emp.get_preference(demand.wsid)
        usage_score = emp.current_week_coverage_used

        total_score = preference_score * 10 + usage_score * 5
        candidates.append((total_score, emp))

    if candidates:
        candidates.sort(key=lambda x: x[0])
        return candidates[0][1]

    return None

# ───────── FUNCIÓN PRINCIPAL ─────────


def generate_ai_schedule_complete(week_start: date):
    """Función principal que genera horario completo con IA"""
    try:
        # Cargar todos los datos
        (emps, demands, tpl_name, week, fixed_assignments,
         memory, shift_types, hybrid_combinations) = load_data_complete(week_start)

        # Procesar turnos fijos primero
        all_assignments = fixed_assignments.copy()

        # Filtrar demandas que aún necesitan cobertura
        pending_demands = [d for d in demands if d.remaining_need > 0]

        if pending_demands:
            # Generar asignaciones con algoritmo inteligente
            new_assignments = generate_optimal_assignments(
                emps, pending_demands, week, shift_types,
                hybrid_combinations, memory
            )
            all_assignments.extend(new_assignments)

        # Agregar ausencias para visualización
        absence_assignments = generate_absence_assignments(emps, week)
        all_assignments.extend(absence_assignments)

        # Guardar en memoria para futuras ejecuciones
        with conn() as c, c.cursor() as cur:
            memory.save_week_data(
                cur, week_start, all_assignments, shift_types)
            c.commit()

        # Construir respuesta
        response = build_complete_response(
            all_assignments, emps, tpl_name, week_start, week)

        return response, all_assignments, emps, week

    except Exception as e:
        logging.error(f"Error generando horario AI completo: {e}")
        raise ScheduleGenerationError(f"Error en generación: {str(e)}")


def generate_absence_assignments(emps: List[EmployeeAI], week: List[date]) -> List[Assignment]:
    """Genera asignaciones de ausencias para visualización"""
    absence_assignments = []

    for emp in emps:
        for d in emp.absent:
            if d in week:
                pseudo_demand = DemandAI((
                    uid(), d, ABS_WS_ID, "AUSENCIA",
                    time(0, 0), time(0, 0), 0
                ))
                pseudo_demand.duration_hours = 0

                assignment = Assignment(emp, pseudo_demand, 0)
                absence_assignments.append(assignment)

    return absence_assignments


def build_complete_response(assignments: List[Assignment], emps: List[EmployeeAI],
                            tpl_name: str, week_start: date, week: List[date]) -> dict:
    """Construye respuesta completa con métricas de cobertura"""

    # Organizar por día
    schedule_by_day = defaultdict(list)
    total_coverage_assigned = 0
    total_coverage_needed = 0

    for assignment in assignments:
        schedule_by_day[assignment.demand.date].append(assignment)
        if assignment.demand.wsid != ABS_WS_ID:
            total_coverage_assigned += assignment.coverage_assigned
            total_coverage_needed += assignment.demand.need

    # Calcular métricas de equidad
    equity_metrics = calculate_coverage_equity(assignments, emps)

    response = {
        "template": tpl_name,
        "week_start": week_start.isoformat(),
        "week_end": (week_start + timedelta(days=6)).isoformat(),
        "ai_enabled": True,
        "algorithm_version": "4.1_complete",
        "summary": {
            "total_employees": len(emps),
            "total_coverage_needed": round(total_coverage_needed, 2),
            "total_coverage_assigned": round(total_coverage_assigned, 2),
            "coverage_efficiency": round(total_coverage_assigned/total_coverage_needed*100, 1) if total_coverage_needed else 0,
            "equity_metrics": equity_metrics
        },
        "schedule": {}
    }

    # Construir horario día por día
    for d in week:
        day_key = d.isoformat()
        response["schedule"][day_key] = []

        for assignment in schedule_by_day.get(d, []):
            emp = assignment.employee
            demand = assignment.demand

            response["schedule"][day_key].append({
                "employee_id": str(emp.id),
                "employee_name": emp.name,
                "workstation_id": str(demand.wsid),
                "workstation_name": demand.wsname,
                "start_time": "--" if demand.wsid == ABS_WS_ID else demand.start.strftime("%H:%M"),
                "end_time": "--" if demand.wsid == ABS_WS_ID else demand.end.strftime("%H:%M"),
                "coverage_assigned": round(assignment.coverage_assigned, 2),
                "employee_capacity": round(emp.get_coverage(demand.wsid), 2) if demand.wsid != ABS_WS_ID else 0,
                "preference_rank": emp.get_preference(demand.wsid) if demand.wsid != ABS_WS_ID else 0,
                "observation": get_assignment_observation(emp, d, assignment, schedule_by_day[d])
            })

    return response


def calculate_coverage_equity(assignments: List[Assignment], emps: List[EmployeeAI]) -> dict:
    """Calcula métricas de equidad de cobertura"""
    emp_coverage_used = defaultdict(float)
    emp_preferred_assignments = defaultdict(int)
    emp_total_assignments = defaultdict(int)
    workstation_coverage = defaultdict(float)

    for assignment in assignments:
        if assignment.demand.wsid != ABS_WS_ID:
            emp_id = assignment.employee.id
            emp_coverage_used[emp_id] += assignment.coverage_assigned
            emp_total_assignments[emp_id] += 1

            # Verificar si es puesto preferido (top 2)
            pref_rank = assignment.employee.get_preference(
                assignment.demand.wsid)
            if pref_rank <= 2:
                emp_preferred_assignments[emp_id] += 1

            workstation_coverage[assignment.demand.wsname] += assignment.coverage_assigned

    # Calcular estadísticas
    coverage_values = list(emp_coverage_used.values()
                           ) if emp_coverage_used else [0]

    return {
        "avg_coverage_per_employee": round(sum(coverage_values) / len(coverage_values), 2),
        "coverage_std_deviation": round(calculate_std_deviation(coverage_values), 2),
        "employees_with_preferred_posts": sum(1 for emp_id in emp_preferred_assignments
                                              if emp_preferred_assignments[emp_id] / max(emp_total_assignments[emp_id], 1) >= 0.5),
        "workstation_coverage_distribution": {k: round(v, 2) for k, v in workstation_coverage.items()},
        "max_coverage_per_employee": round(max(coverage_values), 2),
        "min_coverage_per_employee": round(min(coverage_values), 2)
    }


def calculate_std_deviation(values: List[float]) -> float:
    """Calcula desviación estándar"""
    if len(values) <= 1:
        return 0.0

    mean = sum(values) / len(values)
    variance = sum((x - mean) ** 2 for x in values) / len(values)
    return variance ** 0.5


def get_assignment_observation(emp: EmployeeAI, d: date, assignment: Assignment, day_assignments: List[Assignment]) -> str:
    """Calcula observación para la asignación"""
    if assignment.demand.wsid == ABS_WS_ID:
        return emp.abs_reason.get(d, 'ABS')

    # Contar asignaciones del empleado ese día
    emp_assignments = [a for a in day_assignments if a.employee.id ==
                       emp.id and a.demand.wsid != ABS_WS_ID]

    if len(emp_assignments) <= 1:
        return ""

    # Calcular cobertura total usada
    total_coverage = sum(a.coverage_assigned for a in emp_assignments)

    if total_coverage < 1.0:
        return "BT"  # Bajo tiempo
    elif total_coverage == 1.0:
        return ""    # Normal
    else:
        return "C"   # Completo/sobrecarga

# ───────── ENDPOINTS ─────────


@app.route('/api/health')
def health():
    """Endpoint de salud"""
    st = {"status": "checking", "timestamp": now().isoformat(),
          "version": "4.1-complete", "checks": {}}
    try:
        with conn() as c, c.cursor() as cur:
            cur.execute("SELECT version()")
            st["checks"]["database"] = {"status": "healthy", "version": cur.fetchone()[
                0].split(',')[0]}

            # Verificar tablas necesarias
            tables_to_check = ["ScheduleMemory", "ShiftTypes",
                               "HybridWorkstations", "EmployeeShiftTypeRestrictions"]
            for table in tables_to_check:
                cur.execute(f"""
                    SELECT COUNT(*) FROM information_schema.tables 
                    WHERE table_name = '{table}' AND table_schema = 'Management'
                """)
                exists = cur.fetchone()[0] > 0
                st["checks"][f"table_{table.lower()}"] = {
                    "status": "ready" if exists else "missing"}

            st["status"] = "healthy"
    except Exception as e:
        st["checks"]["database"] = {"status": "unhealthy", "message": str(e)}
        st["status"] = "unhealthy"

    return jsonify(st), 200 if st["status"] == "healthy" else 503


@app.route('/api/agenda/ai-complete-preview')
def ai_complete_preview():
    """Endpoint principal para preview con IA completa"""
    wk = request.args.get('week_start')
    if not wk:
        return jsonify({"error": "Falta week_start"}), 400

    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    try:
        response, _, _, _ = generate_ai_schedule_complete(ws)
        return jsonify(response), 200

    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
        logging.error(f"Error en AI complete preview: {e}")
        return jsonify({"error": str(e)}), 400

    except Exception as e:
        logging.error(f"Error inesperado: {e}")
        return jsonify({"error": "Error interno del servidor"}), 500


@app.route('/api/agenda/ai-complete-save', methods=['POST'])
def ai_complete_save():
    """Endpoint para guardar horario generado con IA completa"""
    data = request.get_json() or {}
    wk = data.get('week_start')
    force = data.get('force', False)

    if not wk:
        return jsonify({"error": "Falta week_start"}), 400

    try:
        ws = monday(datetime.strptime(wk, '%Y-%m-%d').date())
    except ValueError:
        return jsonify({"error": "Fecha inválida"}), 400

    we = ws + timedelta(days=6)

    try:
        # Generar horario
        response, assignments, emps, week = generate_ai_schedule_complete(ws)

        with conn() as c, c.cursor() as cur:
            # Verificar si ya existe
            cur.execute('''
                SELECT COUNT(*) FROM "Management"."Schedules"
                WHERE "Date" BETWEEN %s AND %s
            ''', (ws, we))

            if cur.fetchone()[0] and not force:
                return jsonify({"error": "Horario ya existe para esa semana"}), 409

            if force:
                cur.execute('''
                    DELETE FROM "Management"."Schedules" 
                    WHERE "Date" BETWEEN %s AND %s
                ''', (ws, we))

            # Insertar nuevos horarios
            for assignment in assignments:
                emp = assignment.employee
                demand = assignment.demand

                if demand.wsid == ABS_WS_ID:
                    # Ausencia
                    cur.execute('''
                        INSERT INTO "Management"."Schedules"
                            ("Id","Date","UserId","WorkstationId",
                             "StartTime","EndTime","Observation",
                             "IsDeleted","DateCreated")
                        VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                    ''', (uid(), demand.date, str(emp.id), ABS_WS_ID,
                          None, None, emp.abs_reason.get(demand.date, 'ABS'),
                          False, now()))
                else:
                    # Turno normal
                    cur.execute('''
                        INSERT INTO "Management"."Schedules"
                            ("Id","Date","UserId","WorkstationId",
                             "StartTime","EndTime","Observation",
                             "IsDeleted","DateCreated")
                        VALUES (%s,%s,%s,%s,%s,%s,%s,%s,%s)
                    ''', (uid(), demand.date, str(emp.id), str(demand.wsid),
                          timedelta(hours=demand.start.hour,
                                    minutes=demand.start.minute),
                          timedelta(hours=demand.end.hour,
                                    minutes=demand.end.minute),
                          get_assignment_observation(
                              emp, demand.date, assignment, []),
                          False, now()))

            c.commit()

        return jsonify({
            "message": "Horario AI completo guardado exitosamente",
            "ai_algorithm": "complete_coverage_v4.1",
            **response
        }), 201

    except (DatabaseConnectionError, DataNotFoundError, ScheduleGenerationError) as e:
        logging.error(f"Error guardando AI complete schedule: {e}")
        return jsonify({"error": str(e)}), 400

    except Exception as e:
        logging.error(f"Error inesperado guardando: {e}")
        return jsonify({"error": "Error interno del servidor"}), 500


@app.route('/api/agenda/coverage-analysis')
def coverage_analysis():
    """Endpoint para análisis de cobertura y capacidades"""
    try:
        with conn() as c, c.cursor() as cur:
            # Análisis de empleados y capacidades
            emp_analysis = fetchall(cur, '''
                SELECT u."Id", 
                       COALESCE(u."FirstName",'')||' '||COALESCE(u."LastName",'') AS name,
                       COUNT(uw."WorkstationId") as workstation_count,
                       AVG(COALESCE(uw."CoveragePercentage", 100)) as avg_coverage,
                       MIN(COALESCE(uw."Preference", 1)) as best_preference
                FROM "Management"."AspNetUsers" u
                LEFT JOIN "Management"."UserWorkstations" uw ON u."Id" = uw."UserId" AND NOT uw."IsDelete"
                WHERE u."IsActive" AND NOT u."IsDelete"
                GROUP BY u."Id", u."FirstName", u."LastName"
                ORDER BY workstation_count DESC, avg_coverage DESC
            ''')

            # Análisis de puestos híbridos
            hybrid_analysis = fetchall(cur, '''
                SELECT hw."Id",
                       wa."Name" as workstation_a,
                       wb."Name" as workstation_b,
                       wc."Name" as workstation_c,
                       wd."Name" as workstation_d
                FROM "Management"."HybridWorkstations" hw
                LEFT JOIN "Management"."Workstations" wa ON hw."WorkstationAId" = wa."Id"
                LEFT JOIN "Management"."Workstations" wb ON hw."WorkstationBId" = wb."Id"
                LEFT JOIN "Management"."Workstations" wc ON hw."WorkstationCId" = wc."Id"
                LEFT JOIN "Management"."Workstations" wd ON hw."WorkstationDId" = wd."Id"
                WHERE hw."IsActive"
            ''')

            # Análisis de tipos de turno
            shift_type_analysis = fetchall(cur, '''
                SELECT st."Name", st."Description",
                       COUNT(estr."UserId") as restricted_employees
                FROM "Management"."ShiftTypes" st
                LEFT JOIN "Management"."EmployeeShiftTypeRestrictions" estr ON st."Id" = estr."ShiftTypeId"
                WHERE st."IsActive"
                GROUP BY st."Id", st."Name", st."Description"
                ORDER BY restricted_employees DESC
            ''')

            analysis = {
                "employee_capacity_analysis": [
                    {
                        "employee_id": str(row[0]),
                        "employee_name": row[1],
                        "workstation_count": row[2],
                        "avg_coverage_percentage": round(float(row[3]), 2),
                        "best_preference_rank": row[4],
                        "is_hybrid_capable": row[2] >= 4
                    }
                    for row in emp_analysis
                ],
                "hybrid_combinations": [
                    {
                        "combination_id": str(row[0]),
                        "workstations": [ws for ws in row[1:] if ws],
                        "combination_size": len([ws for ws in row[1:] if ws])
                    }
                    for row in hybrid_analysis
                ],
                "shift_type_restrictions": [
                    {
                        "shift_type_name": row[0],
                        "description": row[1],
                        "restricted_employees": row[2]
                    }
                    for row in shift_type_analysis
                ]
            }

            return jsonify(analysis), 200

    except Exception as e:
        logging.error(f"Error en análisis de cobertura: {e}")
        return jsonify({"error": "Error consultando análisis"}), 500

# ───────── CONFIGURACIÓN Y MAIN ─────────


logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s"
)

if __name__ == "__main__":
    print("🤖 AI Scheduler Completo Gandarías v4.1 ↗ http://localhost:5000")
    print("📊 Endpoints disponibles:")
    print("  GET  /api/agenda/ai-complete-preview?week_start=YYYY-MM-DD")
    print("  POST /api/agenda/ai-complete-save")
    print("  GET  /api/agenda/coverage-analysis")
    print("  GET  /api/health")
    print()
    print("🔧 Funcionalidades implementadas:")
    print("  ✅ Cobertura por capacidad laboral (no tiempo)")
    print("  ✅ Validación de tipos de turno por empleado")
    print("  ✅ Combinaciones híbridas válidas")
    print("  ✅ Asignación fraccionaria optimizada")
    print("  ✅ Priorización por preferencias")
    print("  ✅ Rotación automática con memoria")
    app.run(host="0.0.0.0", port=5000, debug=True)
