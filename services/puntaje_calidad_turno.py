# services/puntaje_calidad_turno.py
"""
HU 1.2 - Puntaje de Calidad del Turno (0..100) — v4.3 (FIX cobertura real)
=========================================================================

PROBLEMA QUE CORRIGE:
  - En algunos entornos, varios puestos aparecían con 0% de cobertura aunque sí estaban cubiertos.
    La causa típica es que el motor de agenda trabaja con demandas normalizadas/mergeadas,
    pero la tabla de calidad/reporting suele esperar la granularidad REAL de WorkstationDemands.

SOLUCIÓN:
  - Para calcular y persistir coverage POR SLOT, este servicio ahora reconstruye la lista de
    demandas desde BD (WorkstationDemands + Workstations) para la semana (ws..we) y calcula
    la cobertura cruzando contra el sched generado (intervalos por WorkstationId).
  - Así, la calidad queda alineada con la estructura real de BD y los dashboards.

NOTA:
  - No requiere cambios en el endpoint. Puedes seguir llamando calcular_y_guardar(...) igual.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, date, time, timedelta
from typing import Any, Dict, List, Tuple, Optional
import json
import math
from uuid import uuid4

from psycopg2.extras import Json

# ============================================================
# DEFAULTS
# ============================================================

DEFAULT_WEIGHTS = {"coverage": 0.60, "fairness": 0.25, "rules": 0.15}
DEFAULT_PARAMS = {"fairness_cv_target": 0.25, "rules_violation_cap": 20}

# ============================================================
# HELPERS
# ============================================================

def _clamp(x: float, lo: float = 0.0, hi: float = 100.0) -> float:
    return lo if x < lo else hi if x > hi else x

def _t2m(t: time) -> int:
    return int(t.hour) * 60 + int(t.minute)

def _to_dt(day: date, t: time) -> datetime:
    return datetime.combine(day, t)

def _merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda it: (it[0], it[1]))
    merged = [list(intervals[0])]
    for s, e in intervals[1:]:
        if s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    return [(a, b) for a, b in merged]

def _interval_min(day: date, st: time, en: time) -> Tuple[int, int]:
    """
    Devuelve (s_min, e_min) relativo al inicio del día.
    Soporta cruces de medianoche (00:00 o fin<=ini).
    """
    ini = _to_dt(day, st)
    fin = _to_dt(day, en)
    if en == time(0, 0) or fin <= ini:
        fin = _to_dt(day + timedelta(days=1), en)
    s_min = int((ini - _to_dt(day, time(0, 0))).total_seconds() // 60)
    e_min = s_min + int((fin - ini).total_seconds() // 60)
    return s_min, e_min

def _as_time_payload(col_udt: str, t: time) -> Any:
    """
    Valor correcto para StartTime/EndTime según tipo real de columna:
      - interval -> timedelta
      - time     -> time
    """
    if t is None:
        return timedelta(0) if col_udt == "interval" else time(0, 0)
    if col_udt == "interval":
        return timedelta(hours=t.hour, minutes=t.minute)
    return t

def _table_columns(cur, schema: str, table: str) -> Dict[str, Dict[str, str]]:
    cur.execute(
        """
        SELECT column_name, data_type, udt_name
        FROM information_schema.columns
        WHERE table_schema = %s AND table_name = %s
        """,
        (schema, table),
    )
    out: Dict[str, Dict[str, str]] = {}
    for col, data_type, udt in cur.fetchall() or []:
        out[str(col)] = {"data_type": str(data_type), "udt": str(udt)}
    return out

def _pick_template_id(cur) -> Tuple[str, str]:
    """
    Replica la lógica del API: 1 activa o error si múltiples activas.
    Fallback: la primera con demandas.
    """
    cur.execute(
        """
        SELECT "Id","Name"
        FROM "Management"."WorkstationDemandTemplates"
        WHERE "IsActive" = TRUE
        """
    )
    act = cur.fetchall() or []
    if len(act) == 1:
        return str(act[0][0]), str(act[0][1])
    if len(act) > 1:
        raise RuntimeError("Hay varias plantillas activas (WorkstationDemandTemplates.IsActive=TRUE)")

    cur.execute(
        """
        SELECT "Id","Name",
               (SELECT COUNT(*) FROM "Management"."WorkstationDemands" d WHERE d."TemplateId" = t."Id") AS demandas
        FROM "Management"."WorkstationDemandTemplates" t
        WHERE "StartDate" IS NOT NULL AND "EndDate" IS NOT NULL
        ORDER BY "StartDate","EndDate","Id"
        """
    )
    rows = cur.fetchall() or []
    if not rows:
        raise RuntimeError("No existen plantillas con demandas")
    chosen = next((r for r in rows if int(r[2] or 0) > 0), None)
    if not chosen:
        raise RuntimeError("No hay plantilla con demandas > 0")
    return str(chosen[0]), str(chosen[1])

def _fetch_demands_week(cur, week_start: date, template_id: str) -> List[Dict[str, Any]]:
    """
    Demandas EXACTAS desde BD para la semana:
      Id, Date, WorkstationId, WorkstationName, StartTime(time), EndTime(time), EffortRequired(float)
    """
    cur.execute(
        """
        SELECT d."Id",
               %s + d."Day"*interval '1 day' AS ddate,
               d."WorkstationId",
               w."Name",
               (TIMESTAMP '2000-01-01'+d."StartTime")::time,
               (TIMESTAMP '2000-01-01'+d."EndTime")::time,
               d."EffortRequired"
        FROM "Management"."WorkstationDemands" d
        JOIN "Management"."Workstations" w ON w."Id" = d."WorkstationId"
        WHERE d."TemplateId" = %s
        ORDER BY d."Day", d."StartTime", d."EndTime", d."Id"
        """,
        (week_start, template_id),
    )
    out: List[Dict[str, Any]] = []
    for did, ddt, wsid, wsname, st, en, eff in cur.fetchall() or []:
        d0 = ddt.date() if hasattr(ddt, "date") else ddt
        out.append(
            {
                "demand_id": str(did) if did is not None else None,
                "date": d0,
                "workstation_id": str(wsid) if wsid is not None else None,
                "workstation_name": str(wsname) if wsname is not None else "UNKNOWN",
                "start": st,
                "end": en,
                "required": float(eff or 0.0),
            }
        )
    return out

def _build_sched_index(sched: Dict[date, List[Tuple[Any, Any]]]) -> Dict[Tuple[date, str], Dict[str, List[Tuple[int, int]]]]:
    """
    Index: (date, workstation_id) -> {emp_id: [(s_min,e_min) ...]}

    Importante: guardamos intervalos por empleado para poder MERGEAR y reconocer cobertura
    aunque el empleado tenga 2+ segmentos consecutivos que juntos cubren el slot.
    """
    idx: Dict[Tuple[date, str], Dict[str, List[Tuple[int, int]]]] = {}
    for d, pairs in (sched or {}).items():
        for emp, dm in pairs:
            if dm is None or getattr(dm, "wsid", None) is None:
                continue
            wsid = str(dm.wsid)
            emp_id = str(getattr(emp, "id", emp))
            s_min, e_min = _interval_min(d, dm.start, dm.end)
            idx.setdefault((d, wsid), {}).setdefault(emp_id, []).append((s_min, e_min))

    # merge por empleado
    for key, per_emp in idx.items():
        for emp_id, intervals in list(per_emp.items()):
            per_emp[emp_id] = _merge_intervals(intervals)

    return idx

def _covered_for_demand(
    d: date,
    wsid: str,
    dem_s: int,
    dem_e: int,
    sched_idx: Dict[Tuple[date, str], Dict[str, List[Tuple[int, int]]]],
) -> Tuple[int, List[str]]:
    """
    Retorna (n_empleados_cubren, empleados_ids) para el slot [dem_s, dem_e].

    Criterio: la UNIÓN de intervalos del empleado (ya mergeada) cubre completamente el slot.
    """
    emps = []
    per_emp = sched_idx.get((d, wsid), {}) or {}
    for emp_id, merged in per_emp.items():
        for s, e in merged:
            if s <= dem_s and e >= dem_e:
                emps.append(emp_id)
                break
    emps = sorted(set(emps))
    return len(emps), emps

# ============================================================
# CONFIG ACTIVE
# ============================================================

def _load_active_config(cur) -> Tuple[Optional[str], Dict[str, Any]]:
    try:
        cur.execute(
            """
            SELECT "Id","Weights","Params"
            FROM "Management"."ScheduleQualityConfig"
            WHERE "IsActive" = true
            ORDER BY "CreatedAt" DESC LIMIT 1
            """
        )
        row = cur.fetchone()
        if not row:
            return None, {"weights": dict(DEFAULT_WEIGHTS), "params": dict(DEFAULT_PARAMS)}

        cfg_id, weights, params = row[0], row[1], row[2]
        if isinstance(weights, str):
            weights = json.loads(weights)
        if isinstance(params, str):
            params = json.loads(params)

        w = dict(DEFAULT_WEIGHTS)
        p = dict(DEFAULT_PARAMS)
        w.update(weights or {})
        p.update(params or {})
        return str(cfg_id), {"weights": w, "params": p}
    except Exception:
        return None, {"weights": dict(DEFAULT_WEIGHTS), "params": dict(DEFAULT_PARAMS)}

# ============================================================
# FAIRNESS / RULES (semanales)
# ============================================================

def _build_employee_minutes_from_sched(sched: Dict[date, List[Tuple[Any, Any]]]) -> Dict[Any, int]:
    minutes_by_emp: Dict[Any, int] = {}
    intervals_by_emp_day: Dict[Tuple[Any, date], List[Tuple[int, int]]] = {}

    for d, pairs in (sched or {}).items():
        for emp, dm in pairs:
            if dm is None or getattr(dm, "wsid", None) is None:
                continue
            s_min, e_min = _interval_min(d, dm.start, dm.end)
            key = (getattr(emp, "id", emp), d)
            intervals_by_emp_day.setdefault(key, []).append((s_min, e_min))

    for (eid, _d), intervals in intervals_by_emp_day.items():
        merged = _merge_intervals(intervals)
        day_minutes = sum(e - s for s, e in merged)
        minutes_by_emp[eid] = minutes_by_emp.get(eid, 0) + int(day_minutes)

    return minutes_by_emp

def _fairness_score(minutes_by_emp: Dict[Any, int], cv_target: float) -> Dict[str, float]:
    values = [m for m in minutes_by_emp.values() if m > 0]
    if len(values) <= 1:
        return {"score": 100.0, "cv": 0.0, "mean": float(values[0] if values else 0.0), "std": 0.0}

    mean = sum(values) / len(values)
    if mean <= 0:
        return {"score": 100.0, "cv": 0.0, "mean": 0.0, "std": 0.0}

    var = sum((v - mean) ** 2 for v in values) / len(values)
    std = math.sqrt(var)
    cv = std / mean

    scaled = 1.0 - min(1.0, cv / max(1e-9, float(cv_target)))
    score = 100.0 * _clamp(scaled, 0.0, 1.0)
    return {"score": score, "cv": cv, "mean": mean, "std": std}

def _rules_violations(sched: Dict[date, List[Tuple[Any, Any]]]) -> Dict[str, Any]:
    overlaps = 0
    outside_window = 0

    for d, pairs in (sched or {}).items():
        by_emp: Dict[Any, List[Tuple[datetime, datetime, Any]]] = {}
        for emp, dm in pairs:
            if dm is None or getattr(dm, "wsid", None) is None:
                continue
            ini = datetime.combine(d, dm.start)
            fin = datetime.combine(d, dm.end)
            if dm.end == time(0, 0) or fin <= ini:
                fin = datetime.combine(d + timedelta(days=1), dm.end)
            by_emp.setdefault(getattr(emp, "id", emp), []).append((ini, fin, dm.wsid))

            fn = getattr(emp, "available", None)
            if callable(fn):
                try:
                    ok = bool(fn(d, dm.start, dm.end))
                except Exception:
                    ok = True
                if not ok:
                    outside_window += 1

        for _, ivs in by_emp.items():
            ivs = sorted(ivs, key=lambda x: (x[0], x[1]))
            for i in range(1, len(ivs)):
                prev_s, prev_e, _ = ivs[i - 1]
                s, _, _ = ivs[i]
                if s < prev_e:
                    overlaps += 1

    return {"overlaps": overlaps, "outside_window": outside_window, "total": overlaps + outside_window}

# ============================================================
# RESULTADO
# ============================================================

@dataclass
class QualityResult:
    score: float
    coverage_score: float
    fairness_score: float
    rules_score: float
    metrics: Dict[str, Any]
    config_id: Optional[str]
    config_snapshot: Dict[str, Any]

# ============================================================
# SERVICIO PRINCIPAL  — FIX v4.3
# ============================================================

class ScheduleQualityService:
    """
    Escribe a "Management"."ScheduleQualityShiftScores" (tabla real en BD).

    FIX v4.3:
      - recalcula coverage por slot usando WorkstationDemands reales en BD + sched,
        evitando falsos 0% por demandas mergeadas/normalizadas.
      - detecta columnas reales del destino (information_schema) para compatibilidad.
    """

    def __init__(self, cur, table_name: str = '"Management"."ScheduleQualityShiftScores"'):
        self.cur = cur
        self.table_name = table_name

        schema = "Management"
        table = "ScheduleQualityShiftScores"
        self._cols = _table_columns(cur, schema=schema, table=table)

        def pick(*cands: str) -> Optional[str]:
            for c in cands:
                if c in self._cols:
                    return c
            return None

        self.col_id = pick("Id")
        self.col_token = pick("Token")
        self.col_demand_id = pick("DemandId", "WorkstationDemandId")
        self.col_date = pick("Date")
        self.col_ws_id = pick("WorkstationId")
        self.col_ws_name = pick("WorkstationName")
        self.col_start = pick("StartTime")
        self.col_end = pick("EndTime")
        self.col_demanded = pick("Demanded", "Required", "EffortRequired")
        self.col_covered = pick("Covered")
        self.col_unmet = pick("Unmet")
        self.col_cov_score = pick("CoverageScore")
        self.col_fair_score = pick("FairnessScore")
        self.col_rules_score = pick("RulesScore")
        self.col_score = pick("Score")
        self.col_metrics = pick("Metrics")
        self.col_cfg = pick("ConfigSnapshot")
        self.col_created = pick("DateCreated", "CreatedAt")
        self.col_is_post_ai = pick("IsPostAi", "IsPostAI")

        required_cols = [self.col_id, self.col_token, self.col_date, self.col_start, self.col_end, self.col_score]
        if any(c is None for c in required_cols):
            raise RuntimeError(
                f"ScheduleQualityShiftScores: columnas obligatorias no encontradas. "
                f"Cols reales={list(self._cols.keys())}"
            )

        self._start_udt = self._cols[self.col_start]["udt"]
        self._end_udt = self._cols[self.col_end]["udt"]

    # ---------------------------
    # Calcular agregado (semanal)
    # ---------------------------

    def calcular(self, required: float, covered: float, sched: Dict[date, Any], emps: List[Any]) -> QualityResult:
        config_id, cfg = _load_active_config(self.cur)
        weights = cfg["weights"]
        params = cfg["params"]

        ratio = 1.0 if required <= 0 else _clamp(covered / required, 0.0, 1.0)
        coverage_score = 100.0 * ratio

        minutes_by_emp = _build_employee_minutes_from_sched(sched)
        fair = _fairness_score(minutes_by_emp, cv_target=float(params.get("fairness_cv_target", 0.25)))
        fairness_score = float(fair["score"])

        viol = _rules_violations(sched)
        cap = float(params.get("rules_violation_cap", 20))
        rules_scaled = 1.0 - min(1.0, float(viol["total"]) / max(1.0, cap))
        rules_score = 100.0 * _clamp(rules_scaled, 0.0, 1.0)

        w_cov = float(weights.get("coverage", 0.60))
        w_fair = float(weights.get("fairness", 0.25))
        w_rules = float(weights.get("rules", 0.15))
        w_sum = max(1e-9, (w_cov + w_fair + w_rules))
        score = (coverage_score * w_cov + fairness_score * w_fair + rules_score * w_rules) / w_sum
        score = _clamp(score, 0.0, 100.0)

        metrics = {
            "coverage": {"required": required, "covered": covered, "ratio": ratio},
            "fairness": {k: fair[k] for k in ("cv", "mean", "std")},
            "rules": viol,
            "minutes_by_emp": {str(k): v for k, v in minutes_by_emp.items()},
        }
        snapshot = {"weights": weights, "params": params}

        return QualityResult(
            score=float(score),
            coverage_score=float(coverage_score),
            fairness_score=float(fairness_score),
            rules_score=float(rules_score),
            metrics=metrics,
            config_id=config_id,
            config_snapshot=snapshot,
        )

    # ---------------------------
    # Persistencia por slot real
    # ---------------------------

    def _insert_row(self, row: Dict[str, Any]) -> None:
        cols = []
        vals = []
        pars = []
        for k, v in row.items():
            if k is None:
                continue
            cols.append(f'"{k}"')
            vals.append("%s")
            pars.append(v)
        sql = f'INSERT INTO {self.table_name} ({", ".join(cols)}) VALUES ({", ".join(vals)})'
        self.cur.execute(sql, tuple(pars))

    def guardar_por_turno_desde_bd(
        self,
        token: str,
        ws: date,
        we: date,
        sched: Dict[date, Any],
        qr: QualityResult,
        is_post_ai: bool = False,
    ) -> int:
        template_id, template_name = _pick_template_id(self.cur)
        demands = _fetch_demands_week(self.cur, week_start=ws, template_id=template_id)

        # Idempotencia: borrar registros previos de esta semana y token (si existen)
        try:
            self.cur.execute(
                f'DELETE FROM {self.table_name} WHERE "{self.col_token}"=%s AND "{self.col_date}" BETWEEN %s AND %s',
                (str(token), ws, we),
            )
        except Exception as _e:
            print(f"[HU1.2] WARN: no se pudo limpiar ScheduleQualityShiftScores para token={token}: {_e}")
        sched_idx = _build_sched_index(sched)

        inserted = 0
        now_dt = datetime.utcnow()
        zero_but_has_assign = 0

        for dm in demands:
            d0: date = dm["date"]
            if d0 < ws or d0 > we:
                continue

            wsid = dm["workstation_id"]
            if not wsid:
                continue

            st: time = dm["start"]
            en: time = dm["end"]
            dem_s, dem_e = _interval_min(d0, st, en)

            n_emp, emp_ids = _covered_for_demand(d0, wsid, dem_s, dem_e, sched_idx)

            required = float(dm["required"] or 0.0)
            covered = 0.0 if required <= 0 else min(required, float(n_emp))
            unmet = 0.0 if required <= 0 else max(0.0, required - covered)

            slot_cov = 100.0 if required <= 0 else _clamp(100.0 * (covered / required), 0.0, 100.0)

            w = qr.config_snapshot["weights"]
            slot_score = _clamp(
                slot_cov * float(w.get("coverage", 0.60))
                + float(qr.fairness_score) * float(w.get("fairness", 0.25))
                + float(qr.rules_score) * float(w.get("rules", 0.15)),
                0.0, 100.0,
            )

            if slot_cov == 0.0 and n_emp > 0:
                zero_but_has_assign += 1

            slot_metrics = {
                "template_id": template_id,
                "template_name": template_name,
                "required": required,
                "covered": covered,
                "unmet": unmet,
                "coverage_pct": slot_cov,
                "employees": emp_ids,
                "raw_n_employees_covering": n_emp,
            }

            row = {
                self.col_id: str(uuid4()),
                self.col_token: str(token),
                self.col_date: d0,
                self.col_start: _as_time_payload(self._start_udt, st),
                self.col_end: _as_time_payload(self._end_udt, en),
                self.col_score: round(float(slot_score), 2),
            }

            if self.col_demand_id:
                row[self.col_demand_id] = dm["demand_id"]
            if self.col_ws_id:
                row[self.col_ws_id] = wsid
            if self.col_ws_name:
                row[self.col_ws_name] = dm["workstation_name"]
            if self.col_demanded:
                row[self.col_demanded] = float(required)
            if self.col_covered:
                row[self.col_covered] = float(covered)
            if self.col_unmet:
                row[self.col_unmet] = float(unmet)
            if self.col_cov_score:
                row[self.col_cov_score] = round(float(slot_cov), 2)
            if self.col_fair_score:
                row[self.col_fair_score] = round(float(qr.fairness_score), 2)
            if self.col_rules_score:
                row[self.col_rules_score] = round(float(qr.rules_score), 2)
            if self.col_metrics:
                row[self.col_metrics] = Json(slot_metrics)
            if self.col_cfg:
                row[self.col_cfg] = Json(qr.config_snapshot)
            if self.col_created:
                row[self.col_created] = now_dt
            if self.col_is_post_ai:
                row[self.col_is_post_ai] = bool(is_post_ai)

            try:
                self._insert_row(row)
                inserted += 1
            except Exception as e:
                print(f'[HU1.2] Error insertando slot score (DemandId={dm["demand_id"]}): {e}')

        if zero_but_has_assign:
            print(f"[HU1.2] WARN: {zero_but_has_assign} slots quedaron con cov=0 pero n_emp>0 "
                  f"(revisar criterio de 'cubre completo').")

        return inserted

    # ---------------------------
    # API pública (la que ya llamas)
    # ---------------------------

    def calcular_y_guardar(
        self,
        token: str,
        ws: date,
        we: date,
        res: Any,
        sched: Dict[date, Any],
        emps: List[Any],
        coverage_stats: Dict[str, Any] = None,   # compat (ignorado)
        is_post_ai: bool = False,
    ) -> Dict[str, Any]:
        """
        Calcula y guarda scores.
        FIX v4.3: la cobertura se recalcula desde BD para evitar falsos 0%.
        """
        print(f"[HU1.2] Iniciando cálculo calidad. token={token} ws={ws} we={we}")

        template_id, _ = _pick_template_id(self.cur)
        demands = _fetch_demands_week(self.cur, week_start=ws, template_id=template_id)
        sched_idx = _build_sched_index(sched)

        required_total = 0.0
        covered_total = 0.0
        unmet_total = 0.0

        for dm in demands:
            d0 = dm["date"]
            if d0 < ws or d0 > we:
                continue
            required = float(dm["required"] or 0.0)
            if required <= 0:
                continue
            required_total += required

            wsid = dm["workstation_id"]
            if not wsid:
                unmet_total += required
                continue

            dem_s, dem_e = _interval_min(d0, dm["start"], dm["end"])
            n_emp, _ = _covered_for_demand(d0, wsid, dem_s, dem_e, sched_idx)
            cov = min(required, float(n_emp))
            covered_total += cov
            unmet_total += max(0.0, required - cov)

        qr = self.calcular(required=required_total, covered=covered_total, sched=sched, emps=emps)
        print(
            f"[HU1.2] Score={qr.score:.2f} "
            f"(cov={qr.coverage_score:.2f}, fair={qr.fairness_score:.2f}, rules={qr.rules_score:.2f}) "
            f"req={required_total:.2f} cov={covered_total:.2f} unmet={unmet_total:.2f}"
        )

        inserted = self.guardar_por_turno_desde_bd(
            token=token,
            ws=ws,
            we=we,
            sched=sched,
            qr=qr,
            is_post_ai=is_post_ai,
        )
        print(f"[HU1.2] Insertados {inserted} registros por slot en BD")

        result = {
            "score": qr.score,
            "breakdown": {
                "coverage": qr.coverage_score,
                "fairness": qr.fairness_score,
                "rules": qr.rules_score,
            },
            "metrics": qr.metrics,
            "config_id": qr.config_id,
            "inserted": inserted,
            "coverage_recalc": {
                "required": required_total,
                "covered": covered_total,
                "unmet": unmet_total,
            },
        }
        print(f"[HU1.2] Guardado en BD OK ({inserted} registros)")
        return result
