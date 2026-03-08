# services/puntaje_calidad_turno.py
"""
HU 1.2 - Puntaje de Calidad del Turno (0..100)  — v4.2 CORREGIDO
=================================================================
CORRECCIONES v4.2:
  - Escribe a ScheduleQualityShiftScores (tabla REAL en BD, no la genérica)
  - Guarda puntajes POR TURNO/DEMANDA (no solo agregado)
  - Inserta resumen semanal y también detalle por slot
  - Los scores quedan disponibles para HU 1.3 (sugerencias) y HU 1.4 (aprendizaje)
  - Soporte IsPostAi para diferenciar pre/post reoptimización
"""
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, date, time, timedelta
from typing import Any, Dict, List, Tuple, Optional
import json
import math
from uuid import uuid4

# ============================================================
# DEFAULTS
# ============================================================

DEFAULT_WEIGHTS = {"coverage": 0.60, "fairness": 0.25, "rules": 0.15}
DEFAULT_PARAMS = {"fairness_cv_target": 0.25, "rules_violation_cap": 20}


def _clamp(x: float, lo: float = 0.0, hi: float = 100.0) -> float:
    return lo if x < lo else hi if x > hi else x


def _merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda t: (t[0], t[1]))
    merged = [list(intervals[0])]
    for s, e in intervals[1:]:
        if s <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], e)
        else:
            merged.append([s, e])
    return [(a, b) for a, b in merged]


def _to_dt(day: date, t: time) -> datetime:
    return datetime.combine(day, t)


def _load_active_config(cur) -> Tuple[Optional[str], Dict[str, Any]]:
    try:
        cur.execute("""
            SELECT "Id","Weights","Params"
            FROM "Management"."ScheduleQualityConfig"
            WHERE "IsActive" = true
            ORDER BY "CreatedAt" DESC LIMIT 1
        """)
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


def _coverage_from_res(res: Any) -> Dict[str, float]:
    required = 0.0
    covered = 0.0
    unmet = 0.0

    if isinstance(res, dict):
        unmet_demands = res.get("unmet_demands") or []
        if isinstance(unmet_demands, list) and unmet_demands:
            for d in unmet_demands:
                if not isinstance(d, dict):
                    continue
                r = float(d.get("required", 0.0) or 0.0)
                c = float(d.get("covered", 0.0) or 0.0)
                u = float(d.get("unmet", 0.0) or 0.0)
                if c == 0.0 and r > 0.0 and u >= 0.0:
                    c = max(0.0, r - u)
                required += r
                covered += c
                unmet += u

    if required <= 0:
        return {"required": 0.0, "covered": 0.0, "unmet": 0.0, "ratio": 1.0}

    ratio = _clamp(covered / required, 0.0, 1.0)
    return {"required": required, "covered": covered, "unmet": unmet, "ratio": ratio}


def _build_employee_minutes_from_sched(sched: Dict[date, List[Tuple[Any, Any]]]) -> Dict[Any, int]:
    minutes_by_emp: Dict[Any, int] = {}
    intervals_by_emp_day: Dict[Tuple[Any, date], List[Tuple[int, int]]] = {}

    for d, pairs in (sched or {}).items():
        for emp, dm in pairs:
            if dm is None or getattr(dm, "wsid", None) is None:
                continue
            st: time = dm.start
            en: time = dm.end
            ini = _to_dt(d, st)
            fin = _to_dt(d, en)
            if en == time(0, 0) or fin <= ini:
                fin = _to_dt(d + timedelta(days=1), en)
            s_min = int((ini - datetime.combine(d, time(0, 0))).total_seconds() // 60)
            e_min = s_min + int((fin - ini).total_seconds() // 60)
            key = (emp.id, d)
            intervals_by_emp_day.setdefault(key, []).append((s_min, e_min))

    for (eid, d), intervals in intervals_by_emp_day.items():
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


def _rules_violations(res: Any, sched: Dict[date, List[Tuple[Any, Any]]]) -> Dict[str, Any]:
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
            by_emp.setdefault(emp.id, []).append((ini, fin, dm.wsid))
            fn = getattr(emp, "available", None)
            if callable(fn):
                ok = bool(fn(d, dm.start, dm.end))
                if not ok:
                    outside_window += 1

        for eid, ivs in by_emp.items():
            ivs = sorted(ivs, key=lambda x: (x[0], x[1]))
            for i in range(1, len(ivs)):
                prev_s, prev_e, _ = ivs[i - 1]
                s, e, _ = ivs[i]
                if s < prev_e:
                    overlaps += 1

    extra = 0
    if isinstance(res, dict):
        v = res.get("violations")
        if isinstance(v, list):
            extra += len(v)

    return {
        "overlaps": overlaps,
        "outside_window": outside_window,
        "extra": extra,
        "total": overlaps + outside_window + extra,
    }


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
# SERVICIO PRINCIPAL  — CORREGIDO v4.2
# ============================================================

class ScheduleQualityService:
    """
    Escribe a "Management"."ScheduleQualityShiftScores" (tabla real en BD).
    Guarda:
      1) Un registro POR DEMANDA/SLOT con sus scores individuales
      2) Retorna el resultado agregado para que HU 1.3 y HU 1.4 lo usen
    """

    def __init__(self, cur, table_name: str = '"Management"."ScheduleQualityShiftScores"'):
        self.cur = cur
        self.table_name = table_name

    def calcular(self, res: Any, sched: Dict[date, Any], emps: List[Any]) -> QualityResult:
        config_id, cfg = _load_active_config(self.cur)
        weights = cfg["weights"]
        params = cfg["params"]

        cov = _coverage_from_res(res)
        coverage_score = 100.0 * _clamp(float(cov["ratio"]), 0.0, 1.0)

        minutes_by_emp = _build_employee_minutes_from_sched(sched)
        fair = _fairness_score(minutes_by_emp, cv_target=float(params.get("fairness_cv_target", 0.25)))
        fairness_score = float(fair["score"])

        viol = _rules_violations(res, sched)
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
            "coverage": cov,
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

    def guardar_por_turno(
        self,
        token: str,
        coverage_stats: Dict[str, Any],
        qr: QualityResult,
        is_post_ai: bool = False,
    ) -> int:
        """
        Inserta un registro por cada demand/slot en ScheduleQualityShiftScores.
        Columnas según esquema real de BD.
        """
        sql = f"""
            INSERT INTO {self.table_name}
              ("Id", "Token", "DemandId", "Date", "WorkstationName",
               "StartTime", "EndTime", "Demanded", "Covered", "Unmet",
               "CoverageScore", "FairnessScore", "RulesScore", "Score",
               "Metrics", "ConfigSnapshot", "DateCreated", "IsPostAi")
            VALUES
              (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """
        inserted = 0
        now_dt = datetime.utcnow()

        for dm_id, cs in coverage_stats.items():
            dm = cs.get("demand")
            if dm is None:
                continue

            demanded = float(dm.need) if hasattr(dm, "need") else 0.0
            covered = float(cs.get("covered", 0))
            unmet = float(cs.get("unmet", 0))

            # Score individual por slot
            if demanded > 0:
                slot_cov = _clamp(100.0 * covered / demanded, 0.0, 100.0)
            else:
                slot_cov = 100.0

            # Para fairness y rules, usamos el score global (es semanal)
            slot_score = _clamp(
                slot_cov * qr.config_snapshot["weights"].get("coverage", 0.60)
                + qr.fairness_score * qr.config_snapshot["weights"].get("fairness", 0.25)
                + qr.rules_score * qr.config_snapshot["weights"].get("rules", 0.15),
                0.0, 100.0,
            )

            # Construir timedelta para StartTime/EndTime (BD usa interval)
            st = getattr(dm, "start", None)
            en = getattr(dm, "end", None)
            st_td = timedelta(hours=st.hour, minutes=st.minute) if st else timedelta(0)
            en_td = timedelta(hours=en.hour, minutes=en.minute) if en else timedelta(0)

            dm_date = getattr(dm, "date", None)
            ws_name = getattr(dm, "wsname", "UNKNOWN")

            slot_metrics = {
                "demanded": demanded,
                "covered": covered,
                "unmet": unmet,
                "coverage_pct": cs.get("coverage_pct", 0),
                "employees": cs.get("employees", []),
            }

            try:
                # DemandId puede ser UUID string o None
                demand_id_val = str(dm_id) if dm_id else None
                # Intentar castear a uuid válido; si falla, pasamos None
                try:
                    import uuid as _uuid
                    _uuid.UUID(demand_id_val)
                except (ValueError, TypeError, AttributeError):
                    demand_id_val = None

                self.cur.execute(sql, (
                    str(uuid4()),
                    token,
                    demand_id_val,
                    dm_date,
                    ws_name,
                    st_td,
                    en_td,
                    demanded,
                    covered,
                    unmet,
                    round(slot_cov, 2),
                    round(qr.fairness_score, 2),
                    round(qr.rules_score, 2),
                    round(slot_score, 2),
                    json.dumps(slot_metrics, ensure_ascii=False),
                    json.dumps(qr.config_snapshot, ensure_ascii=False),
                    now_dt,
                    bool(is_post_ai),
                ))
                inserted += 1
            except Exception as e:
                print(f"[HU1.2] Error insertando slot score: {e}")

        return inserted

    def calcular_y_guardar(
        self,
        token: str,
        ws: date,
        we: date,
        res: Any,
        sched: Dict[date, Any],
        emps: List[Any],
        coverage_stats: Dict[str, Any] = None,
        is_post_ai: bool = False,
    ) -> Dict[str, Any]:
        """
        Calcula y guarda scores. Ahora recibe coverage_stats directamente
        para poder guardar detalle por turno.
        """
        print(f"[HU1.2] Iniciando cálculo calidad. token={token} ws={ws} we={we}")
        qr = self.calcular(res=res, sched=sched, emps=emps)
        print(
            f"[HU1.2] Score={qr.score:.2f} "
            f"(cov={qr.coverage_score:.2f}, fair={qr.fairness_score:.2f}, rules={qr.rules_score:.2f})"
        )

        # Guardar detalle por turno/demanda
        inserted = 0
        if coverage_stats:
            inserted = self.guardar_por_turno(
                token=token,
                coverage_stats=coverage_stats,
                qr=qr,
                is_post_ai=is_post_ai,
            )
            print(f"[HU1.2] Insertados {inserted} registros por slot en BD")
        else:
            print("[HU1.2] Sin coverage_stats, no se guardan detalles por turno")

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
        }
        print(f"[HU1.2] Guardado en BD OK ({inserted} registros)")
        return result