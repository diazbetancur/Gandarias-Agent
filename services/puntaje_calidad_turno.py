# services/puntaje_calidad_turno.py
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, date, time, timedelta
from typing import Any, Dict, List, Tuple, Optional
import json
import math

# ============================================================
# HU 1.2 - Puntaje de Calidad del Turno (0..100)
# Subscores:
#   - CoverageScore: cobertura (1 - unmet/required)
#   - FairnessScore: equidad (CV de minutos trabajados por empleado)
#   - RulesScore: respeto de reglas (penaliza violaciones detectables)
# Configurable en BD: ScheduleQualityConfig
# ============================================================

DEFAULT_WEIGHTS = {"coverage": 0.60, "fairness": 0.25, "rules": 0.15}
DEFAULT_PARAMS = {"fairness_cv_target": 0.25, "rules_violation_cap": 20}


def _clamp(x: float, lo: float, hi: float) -> float:
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
    """
    Retorna (config_id, config_dict)
    config_dict = {"weights": {...}, "params": {...}}
    """
    try:
        cur.execute(
            """
            SELECT "Id","Weights","Params"
            FROM "Management"."ScheduleQualityConfig"
            WHERE "IsActive" = true
            ORDER BY "CreatedAt" DESC
            LIMIT 1
            """
        )
        row = cur.fetchone()
        if not row:
            return None, {"weights": dict(DEFAULT_WEIGHTS), "params": dict(DEFAULT_PARAMS)}

        cfg_id, weights, params = row[0], row[1], row[2]

        # psycopg2 puede traer jsonb como dict o como string; soportamos ambos
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
        # fallback duro
        return None, {"weights": dict(DEFAULT_WEIGHTS), "params": dict(DEFAULT_PARAMS)}


def _coverage_from_res(res: Any) -> Dict[str, float]:
    """
    Busca coverage en res:
      - unmet_demands: [{required, covered, unmet}, ...]
      - unmet_segments: puede no traer required, así que no siempre sirve
    """
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

                # a veces no viene "covered" pero sí required/unmet
                if c == 0.0 and r > 0.0 and u >= 0.0:
                    c = max(0.0, r - u)

                required += r
                covered += c
                unmet += u

    if required <= 0:
        # sin demanda -> lo tratamos como 100% cobertura
        return {"required": 0.0, "covered": 0.0, "unmet": 0.0, "ratio": 1.0}

    ratio = _clamp(covered / required, 0.0, 1.0)
    return {"required": required, "covered": covered, "unmet": unmet, "ratio": ratio}


def _build_employee_minutes_from_sched(sched: Dict[date, List[Tuple[Any, Any]]]) -> Dict[Any, int]:
    """
    Calcula minutos REALES por empleado en la semana:
      - ignora wsid None
      - fusiona intervalos solapados por día (evita doble conteo híbridos)
    Espera:
      sched[d] = [(emp, dm), ...]
      dm.start/dm.end son time
      dm.wsid identifica estación
    """
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
    """
    CV = std/mean. Menor CV => más equidad.
    Score = 100 * (1 - min(1, CV/cv_target))
    """
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
    """
    Violaciones detectables sin meternos a CP-SAT:
      - overlaps por empleado/día (si hay intervalos que se solapan)
      - asignaciones fuera de ventana (si emp.available existe)
      - daily cap excedido (si MAX_HOURS_PER_DAY viene en res/params no lo tenemos aquí => solo contamos overlaps/outside)
    Nota: si en el futuro tu generate devuelve "violations", puedes sumar aquí.
    """
    overlaps = 0
    outside_window = 0

    # overlaps + outside_window
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

            # fuera de ventana (si existe emp.available(day, st, en))
            fn = getattr(emp, "available", None)
            if callable(fn):
                ok = bool(fn(d, dm.start, dm.end))
                if not ok:
                    outside_window += 1

        # solapes por empleado
        for eid, ivs in by_emp.items():
            ivs = sorted(ivs, key=lambda x: (x[0], x[1]))
            for i in range(1, len(ivs)):
                prev_s, prev_e, _ = ivs[i - 1]
                s, e, _ = ivs[i]
                if s < prev_e:
                    overlaps += 1

    # Si res trae violaciones explícitas, súmalas
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


@dataclass
class QualityResult:
    score: float
    coverage_score: float
    fairness_score: float
    rules_score: float
    metrics: Dict[str, Any]
    config_id: Optional[str]
    config_snapshot: Dict[str, Any]


class ScheduleQualityService:
    def __init__(
        self,
        cur,
        table_name: str = '"Management"."ScheduleQualityScores"',
    ):
        self.cur = cur
        self.table_name = table_name

    def calcular(self, res: Any, sched: Dict[date, Any], emps: List[Any]) -> QualityResult:
        config_id, cfg = _load_active_config(self.cur)
        weights = cfg["weights"]
        params = cfg["params"]

        # 1) Coverage
        cov = _coverage_from_res(res)
        coverage_score = 100.0 * _clamp(float(cov["ratio"]), 0.0, 1.0)

        # 2) Fairness
        minutes_by_emp = _build_employee_minutes_from_sched(sched)
        fair = _fairness_score(minutes_by_emp, cv_target=float(params.get("fairness_cv_target", 0.25)))
        fairness_score = float(fair["score"])

        # 3) Rules
        viol = _rules_violations(res, sched)
        cap = float(params.get("rules_violation_cap", 20))
        rules_scaled = 1.0 - min(1.0, float(viol["total"]) / max(1.0, cap))
        rules_score = 100.0 * _clamp(rules_scaled, 0.0, 1.0)

        # 4) Total
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
            "minutes_by_emp": minutes_by_emp,  # si quieres, luego lo quitas para que no sea pesado
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

    def guardar(self, token: str, ws: date, we: date, qr: QualityResult) -> None:
        sql = f"""
        INSERT INTO {self.table_name}
          ("Token","WeekStart","WeekEnd","Score","CoverageScore","FairnessScore","RulesScore","Metrics","ConfigId","ConfigSnapshot")
        VALUES
          (%s,%s,%s,%s,%s,%s,%s,%s,%s,%s)
        ON CONFLICT ("Token")
        DO UPDATE SET
          "WeekStart"=EXCLUDED."WeekStart",
          "WeekEnd"=EXCLUDED."WeekEnd",
          "Score"=EXCLUDED."Score",
          "CoverageScore"=EXCLUDED."CoverageScore",
          "FairnessScore"=EXCLUDED."FairnessScore",
          "RulesScore"=EXCLUDED."RulesScore",
          "Metrics"=EXCLUDED."Metrics",
          "ConfigId"=EXCLUDED."ConfigId",
          "ConfigSnapshot"=EXCLUDED."ConfigSnapshot",
          "CreatedAt"=now()
        """
        self.cur.execute(
            sql,
            (
                token,
                ws,
                we,
                qr.score,
                qr.coverage_score,
                qr.fairness_score,
                qr.rules_score,
                json.dumps(qr.metrics, ensure_ascii=False),
                qr.config_id,
                json.dumps(qr.config_snapshot, ensure_ascii=False),
            ),
        )

    def calcular_y_guardar(self, token: str, ws: date, we: date, res: Any, sched: Dict[date, Any], emps: List[Any]) -> Dict[str, Any]:
        print(f"[HU1.2] Iniciando cálculo calidad. token={token} ws={ws} we={we}")
        qr = self.calcular(res=res, sched=sched, emps=emps)
        print(
            f"[HU1.2] Score={qr.score:.2f} "
            f"(cov={qr.coverage_score:.2f}, fair={qr.fairness_score:.2f}, rules={qr.rules_score:.2f})"
        )
        self.guardar(token=token, ws=ws, we=we, qr=qr)
        print("[HU1.2] Guardado en BD OK ✅")
        return {
            "score": qr.score,
            "breakdown": {
                "coverage": qr.coverage_score,
                "fairness": qr.fairness_score,
                "rules": qr.rules_score,
            },
            "metrics": qr.metrics,
            "config_id": qr.config_id,
        }
