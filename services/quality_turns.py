# services/quality_turns.py
from __future__ import annotations
from dataclasses import dataclass
from datetime import datetime, date, time, timedelta
from typing import Any, Dict, Optional
import json

def _clamp(x: float, a: float = 0.0, b: float = 100.0) -> float:
    return max(a, min(b, x))

@dataclass
class TurnQualityResult:
    score: float
    coverage: float
    fairness: float
    rules: float
    metrics: Dict[str, Any]

class TurnQualityService:
    """
    Calcula puntaje por TURNO.
    - Turno asignado: se evalúa por obs (BT/C/...), fairness simple por carga, cobertura=100.
    - Turno gap/no asignado: cobertura baja/0, rules baja, fairness no aplica -> 0/100 según config.
    """
    def __init__(
        self,
        cursor,
        table_name: str = '"Management"."ScheduleQualityTurns"',
        weights: Optional[Dict[str, float]] = None,
        rules_map: Optional[Dict[str, float]] = None,
    ):
        self.cur = cursor
        self.table = table_name

        # Pesos default (ajustables)
        self.weights = weights or {"coverage": 0.50, "fairness": 0.30, "rules": 0.20}

        # Mapa de rules por Observation de tu save(): "" / "BT" / "C" / "ABS"
        # (ABS normalmente no cuenta como turno real; pero por si lo guardas)
        self.rules_map = rules_map or {
            "": 100.0,
            "C": 85.0,
            "BT": 60.0,
            "ABS": 0.0,
        }

    # --------------------
    # 1) SCORING ASIGNADO
    # --------------------
    def score_assigned_turn(
        self,
        obs: str,
        emp_minutes_week: int,
        avg_minutes_week: float,
    ) -> TurnQualityResult:
        coverage = 100.0

        # fairness: penaliza si el empleado va muy por encima del promedio semanal
        # (simple, pero útil para comparar versiones)
        if avg_minutes_week <= 0:
            fairness = 100.0
            over_ratio = 0.0
        else:
            over = max(0.0, emp_minutes_week - avg_minutes_week)
            over_ratio = over / avg_minutes_week  # 0.0 = ok, 1.0 = duplica el promedio
            # Si se pasa mucho, baja el score (cap a 0)
            fairness = _clamp(100.0 * (1.0 - over_ratio))

        rules = float(self.rules_map.get(obs or "", 80.0))

        w = self.weights
        score = (coverage * w["coverage"]) + (fairness * w["fairness"]) + (rules * w["rules"])
        score = _clamp(score)

        return TurnQualityResult(
            score=score,
            coverage=coverage,
            fairness=fairness,
            rules=rules,
            metrics={
                "obs": obs,
                "emp_minutes_week": emp_minutes_week,
                "avg_minutes_week": avg_minutes_week,
                "over_ratio": over_ratio,
            },
        )

    # --------------------
    # 2) SCORING GAP
    # --------------------
    def score_gap_turn(self, required: float, covered: float) -> TurnQualityResult:
        # cobertura = covered/required
        if required <= 0:
            coverage = 100.0
            cov_pct = 1.0
        else:
            cov_pct = max(0.0, min(1.0, covered / required))
            coverage = 100.0 * cov_pct

        # fairness: no aplica al gap. Lo dejamos 0 para que el total baje por coverage.
        fairness = 0.0

        # rules: gap => bajo
        rules = 0.0

        w = self.weights
        score = (coverage * w["coverage"]) + (fairness * w["fairness"]) + (rules * w["rules"])
        score = _clamp(score)

        return TurnQualityResult(
            score=score,
            coverage=coverage,
            fairness=fairness,
            rules=rules,
            metrics={"required": required, "covered": covered, "coverage_pct": cov_pct},
        )

    # --------------------
    # 3) PERSISTENCIA
    # --------------------
    def insert_turn(
        self,
        token: str,
        d: date,
        wsid: Any,
        start_t: time,
        end_t: time,
        user_id: Optional[Any],
        is_gap: bool,
        q: TurnQualityResult,
    ) -> None:
        sql = f'''
            INSERT INTO {self.table}
              ("Token","Date","WorkstationId","StartTime","EndTime","UserId","IsGap",
               "Score","CoverageScore","FairnessScore","RulesScore","Metrics")
            VALUES
              (%s,%s,%s,%s,%s,%s,%s,
               %s,%s,%s,%s,%s)
            ON CONFLICT ("Token","Date","WorkstationId","StartTime","EndTime","UserId","IsGap")
            DO UPDATE SET
              "Score"=EXCLUDED."Score",
              "CoverageScore"=EXCLUDED."CoverageScore",
              "FairnessScore"=EXCLUDED."FairnessScore",
              "RulesScore"=EXCLUDED."RulesScore",
              "Metrics"=EXCLUDED."Metrics"
        '''
        self.cur.execute(
            sql,
            (
                str(token),
                d,
                None if wsid is None else str(wsid),
                start_t,
                end_t,
                None if user_id is None else str(user_id),
                bool(is_gap),
                round(q.score, 2),
                round(q.coverage, 2),
                round(q.fairness, 2),
                round(q.rules, 2),
                json.dumps(q.metrics, ensure_ascii=False),
            ),
        )
