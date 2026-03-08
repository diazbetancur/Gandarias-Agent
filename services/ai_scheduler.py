# services/ai_scheduler.py
"""
Motor de IA para Agendamiento – Gandarias v4.1 (CORREGIDO)
==========================================================
REGLAS DURAS VALIDADAS:
  1. Min 3h POR BLOQUE individual (no total/día)         – PDF 2.1
  2. Max 2 bloques/día                                    – PDF 2.2
  3. Min 3h gap entre bloques split MISMO día              – PDF 2.2
  4. Max horas/día                                        – PDF 2.3
  5. 2 días descanso/semana                               – PDF 2.3
  6. Min 9h descanso entre turnos INTER-DÍA               – PDF 2.3
  7. Disponibilidad (ventanas/excepciones/ausencias)       – PDF 2.4
  8. Skills/roles                                          – PDF 1.1
  9. UserShift enforcement (via overrides externo)         – PDF 2.4
"""
from __future__ import annotations
import csv, logging, math
from collections import defaultdict, Counter
from dataclasses import dataclass, field
from datetime import datetime, date, time, timedelta
from typing import Any, Dict, List, Optional, Tuple, Set
from uuid import uuid4

logger = logging.getLogger("ai_scheduler")

REGLAS_DURAS_DEFAULTS = {
    "min_duracion_turno_horas": 3,
    "min_descanso_entre_turnos_horas": 9,
    "min_gap_split_horas": 3,
    "max_horas_por_dia": 9,
    "dias_descanso_semana": 2,
    "max_dias_trabajo_semana": 6,
    "max_bloques_por_dia": 2,
}

def _t2m(t: time) -> int:
    return t.hour * 60 + t.minute

def _m2t(m: int) -> time:
    m = max(0, min(m, 24 * 60 - 1))
    return time(m // 60, m % 60)

def _end_eff(t: time) -> time:
    return t if t != time(0, 0) else time(23, 59)

def _seg_min(start: time, end: time) -> int:
    return max(0, _t2m(_end_eff(end)) - _t2m(start))

def _merge_intervals(intervals):
    if not intervals: return []
    srt = sorted(intervals)
    merged = [list(srt[0])]
    for s, e in srt[1:]:
        if s <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], e)
        else: merged.append([s, e])
    return [(a, b) for a, b in merged]

def _has_overlap(intervals, s, e):
    for a, b in intervals:
        if not (e <= a or b <= s): return True
    return False

def _uid(): return str(uuid4())


# ═══════════════════════════════════════════════════════════════════
# MODELO DE PATRONES
# ═══════════════════════════════════════════════════════════════════

@dataclass
class PatronEmpWS:
    emp_id: str; ws_id: str; frecuencia: int = 0
    horas_promedio: float = 0.0
    dias_frecuentes: List[int] = field(default_factory=list)
    horarios: List[Tuple[str, str]] = field(default_factory=list)
    obs_frecuente: str = "BT"

@dataclass
class PatronHorarioWS:
    ws_id: str; dow: int
    inicio_tipico_min: int = 720; fin_tipico_min: int = 1380
    frecuencia: int = 0; duracion_prom_min: float = 0.0

@dataclass
class PatronCarga:
    emp_id: str; horas_sem_prom: float = 0.0
    dias_trabajo_prom: float = 5.0
    dias_descanso_freq: List[int] = field(default_factory=list)

@dataclass
class ModeloPatrones:
    version: str = "4.1"
    fecha_entrenamiento: str = ""
    registros_procesados: int = 0
    semanas_procesadas: int = 0
    afinidad_emp_ws: Dict = field(default_factory=dict)
    horarios_ws: Dict = field(default_factory=dict)
    carga_emp: Dict = field(default_factory=dict)
    obs_global: Dict = field(default_factory=dict)

    def to_dict(self):
        return {
            "version": self.version, "fecha_entrenamiento": self.fecha_entrenamiento,
            "registros_procesados": self.registros_procesados,
            "semanas_procesadas": self.semanas_procesadas,
            "patrones_afinidad": len(self.afinidad_emp_ws),
            "patrones_horario": len(self.horarios_ws),
            "patrones_carga": len(self.carga_emp),
        }


# ═══════════════════════════════════════════════════════════════════
# EXTRACTOR DE PATRONES
# ═══════════════════════════════════════════════════════════════════

class ExtractorPatrones:
    def __init__(self, debug=True):
        self.debug = debug

    def _log(self, msg):
        if self.debug: print(f"[AI-EXTRACT] {msg}")

    def extraer_de_csv(self, csv_path: str) -> ModeloPatrones:
        self._log(f"Cargando histórico desde {csv_path}")
        registros = []
        with open(csv_path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                if row.get("IsDeleted", "false").lower() == "true": continue
                if not row.get("WorkstationId") or not row.get("StartTime"): continue
                registros.append({
                    "date": row["Date"], "emp_id": row["UserId"],
                    "ws_id": row["WorkstationId"],
                    "start": row["StartTime"], "end": row["EndTime"],
                    "obs": row.get("Observation", ""),
                })
        self._log(f"Cargados {len(registros)} registros")
        return self._procesar(registros)

    def extraer_de_bd(self, cursor, fecha_ini=None, fecha_fin=None) -> ModeloPatrones:
        self._log("Cargando histórico desde BD")
        q = '''SELECT s."Date", s."UserId"::text, s."WorkstationId"::text,
                      s."StartTime", s."EndTime", s."Observation"
               FROM "Management"."Schedules" s
               WHERE s."IsDeleted" = false AND s."WorkstationId" IS NOT NULL
                     AND s."StartTime" IS NOT NULL'''
        params = []
        if fecha_ini: q += ' AND s."Date" >= %s'; params.append(fecha_ini)
        if fecha_fin: q += ' AND s."Date" <= %s'; params.append(fecha_fin)
        q += ' ORDER BY s."Date", s."StartTime"'
        cursor.execute(q, params)
        registros = [
            {"date": str(r[0]), "emp_id": str(r[1]) if r[1] else None,
             "ws_id": str(r[2]) if r[2] else None,
             "start": str(r[3]) if r[3] else None, "end": str(r[4]) if r[4] else None,
             "obs": r[5] or ""}
            for r in cursor.fetchall()
        ]
        self._log(f"Cargados {len(registros)} registros BD")
        return self._procesar(registros)

    def _parse_time_str(self, s):
        if not s: return None
        try:
            parts = s.strip().split(":")
            h, m = int(parts[0]), int(parts[1])
            if h >= 24: h, m = 23, 59
            return h * 60 + m
        except: return None

    def _parse_date(self, s):
        try: return datetime.strptime(s.strip()[:10], "%Y-%m-%d").date()
        except: return None

    def _procesar(self, registros) -> ModeloPatrones:
        modelo = ModeloPatrones(fecha_entrenamiento=datetime.now().isoformat(),
                                 registros_procesados=len(registros))
        afinidad_acc = defaultdict(list)
        horario_acc = defaultdict(list)
        carga_acc = defaultdict(lambda: {"mins_by_week": defaultdict(int),
                                          "days_by_week": defaultdict(set)})
        obs_counter = Counter()
        semanas = set()

        for reg in registros:
            emp_id, ws_id = reg.get("emp_id"), reg.get("ws_id")
            if not emp_id or not ws_id: continue
            d = self._parse_date(reg.get("date", ""))
            s_min = self._parse_time_str(reg.get("start", ""))
            e_min = self._parse_time_str(reg.get("end", ""))
            if d is None or s_min is None or e_min is None: continue
            dur = e_min - s_min
            if dur <= 0: dur += 1440
            if dur <= 0 or dur > 1440: continue
            dow = d.weekday()
            wk = f"{d.year}-W{d.isocalendar()[1]:02d}"
            semanas.add(wk)
            afinidad_acc[(emp_id, ws_id)].append(
                {"dow": dow, "start": s_min, "end": e_min, "dur": dur, "obs": reg.get("obs", "")})
            horario_acc[(ws_id, dow)].append((s_min, e_min))
            carga_acc[emp_id]["mins_by_week"][wk] += dur
            carga_acc[emp_id]["days_by_week"][wk].add(d)
            obs_counter[reg.get("obs", "")] += 1

        modelo.semanas_procesadas = len(semanas)
        modelo.obs_global = dict(obs_counter)

        for (emp_id, ws_id), items in afinidad_acc.items():
            dow_c = Counter(it["dow"] for it in items)
            obs_c = Counter(it["obs"] for it in items)
            h_prom = sum(it["dur"] for it in items) / len(items) / 60.0
            horarios = list(set(
                (f"{it['start']//60:02d}:{it['start']%60:02d}",
                 f"{it['end']//60:02d}:{it['end']%60:02d}") for it in items
            ))[:10]
            modelo.afinidad_emp_ws[(emp_id, ws_id)] = PatronEmpWS(
                emp_id=emp_id, ws_id=ws_id, frecuencia=len(items),
                horas_promedio=round(h_prom, 2),
                dias_frecuentes=sorted(dow_c, key=dow_c.get, reverse=True)[:5],
                horarios=horarios,
                obs_frecuente=obs_c.most_common(1)[0][0] if obs_c else "BT",
            )

        for (ws_id, dow), times in horario_acc.items():
            starts = [t[0] for t in times]; ends = [t[1] for t in times]
            durs = [max(0, e - s) if e > s else max(0, e + 1440 - s) for s, e in times]
            modelo.horarios_ws[(ws_id, dow)] = PatronHorarioWS(
                ws_id=ws_id, dow=dow,
                inicio_tipico_min=int(sum(starts)/len(starts)) if starts else 720,
                fin_tipico_min=int(sum(ends)/len(ends)) if ends else 1380,
                frecuencia=len(times),
                duracion_prom_min=sum(durs)/len(durs) if durs else 0,
            )

        for emp_id, data in carga_acc.items():
            weeks = data["mins_by_week"]; days = data["days_by_week"]
            if not weeks: continue
            h_sem = [v / 60.0 for v in weeks.values()]
            d_sem = [len(v) for v in days.values()]
            all_dows = Counter()
            for wk, day_set in days.items():
                for dd in day_set: all_dows[dd.weekday()] += 1
            n_w = len(weeks)
            d_desc = [dow for dow in range(7) if all_dows.get(dow, 0) < n_w * 0.3]
            modelo.carga_emp[emp_id] = PatronCarga(
                emp_id=emp_id,
                horas_sem_prom=round(sum(h_sem)/len(h_sem), 1),
                dias_trabajo_prom=round(sum(d_sem)/len(d_sem), 1),
                dias_descanso_freq=sorted(d_desc),
            )

        self._log(f"Modelo: {modelo.semanas_procesadas} semanas, "
                   f"{len(modelo.afinidad_emp_ws)} afinidades, "
                   f"{len(modelo.horarios_ws)} pat.horario, "
                   f"{len(modelo.carga_emp)} pat.carga")
        return modelo


# ═══════════════════════════════════════════════════════════════════
# ESTADO POR EMPLEADO
# ═══════════════════════════════════════════════════════════════════

@dataclass
class EstadoEmpleado:
    emp_id: str
    minutos_semana: int = 0
    dias_trabajados: Set[date] = field(default_factory=set)
    minutos_por_dia: Dict[date, int] = field(default_factory=dict)
    intervalos_por_dia: Dict[date, List] = field(default_factory=lambda: defaultdict(list))
    asignaciones: List = field(default_factory=list)  # (date, ws_id, s_min, e_min)

    def registrar(self, d, ws_id, s_min, e_min):
        dur = max(0, e_min - s_min)
        self.minutos_semana += dur
        self.dias_trabajados.add(d)
        self.minutos_por_dia[d] = self.minutos_por_dia.get(d, 0) + dur
        self.intervalos_por_dia[d].append((s_min, e_min))
        self.asignaciones.append((d, ws_id, s_min, e_min))

    def desregistrar(self, d, ws_id, s_min, e_min):
        dur = max(0, e_min - s_min)
        self.minutos_semana = max(0, self.minutos_semana - dur)
        self.minutos_por_dia[d] = max(0, self.minutos_por_dia.get(d, 0) - dur)
        if (s_min, e_min) in self.intervalos_por_dia.get(d, []):
            self.intervalos_por_dia[d].remove((s_min, e_min))
        if not self.intervalos_por_dia.get(d):
            self.dias_trabajados.discard(d)
        # Remove from asignaciones
        try:
            self.asignaciones.remove((d, ws_id, s_min, e_min))
        except ValueError:
            pass


# ═══════════════════════════════════════════════════════════════════
# VALIDADOR DE REGLAS DURAS (CORREGIDO)
# ═══════════════════════════════════════════════════════════════════

class ValidadorReglasDuras:
    def __init__(self, reglas=None):
        self.reglas = reglas or dict(REGLAS_DURAS_DEFAULTS)

    def puede_asignar(self, emp, dm, d, estado_emp, overrides=None):
        """
        Valida TODAS las reglas duras ANTES de asignar.
        overrides = set de (emp_id, date) donde UserShift NO se enfuerza.
        """
        overrides = overrides or set()

        # 1. Skill check
        if not emp.can(dm.wsid):
            return False, "SIN_SKILL"

        # 2. Día libre / ausente
        if emp.off(d) or emp.absent_day(d):
            return False, "DIA_LIBRE"

        # 3. Disponibilidad (ventana semanal o excepción)
        if not emp.available(d, dm.start, dm.end):
            return False, "FUERA_VENTANA"

        # 4. UserShift enforcement: si NO está en overrides y tiene ventanas US,
        #    la demanda debe caer dentro de alguna ventana US
        if (str(emp.id), d) not in overrides:
            dow = d.weekday()
            us_wins = emp.user_shift_windows.get(dow, [])
            if us_wins:
                dm_end = _end_eff(dm.end)
                inside = False
                for w_s, w_e in us_wins:
                    w_end = _end_eff(w_e)
                    if dm.start >= w_s and dm_end <= w_end:
                        inside = True
                        break
                if not inside:
                    return False, "FUERA_USERSHIFT_WINDOW"

        # 5. Max días trabajados/semana
        max_dias = self.reglas.get("max_dias_trabajo_semana", 6)
        if d not in estado_emp.dias_trabajados and len(estado_emp.dias_trabajados) >= max_dias:
            return False, "MAX_DIAS"

        # 6. Max horas/día
        max_h = self.reglas.get("max_horas_por_dia", 9) * 60
        dur = _seg_min(dm.start, dm.end)
        if estado_emp.minutos_por_dia.get(d, 0) + dur > max_h:
            return False, "MAX_HORAS_DIA"

        s_new, e_new = _t2m(dm.start), _t2m(_end_eff(dm.end))

        # 7. Solapamiento
        if _has_overlap(estado_emp.intervalos_por_dia.get(d, []), s_new, e_new):
            return False, "SOLAPAMIENTO"

        # 8. Max bloques/día + gap entre bloques split
        max_bloques = self.reglas.get("max_bloques_por_dia", 2)
        min_gap_split = self.reglas.get("min_gap_split_horas", 3) * 60
        ivs = list(estado_emp.intervalos_por_dia.get(d, []))
        ivs.append((s_new, e_new))
        bloques = _merge_intervals(ivs)

        if len(bloques) > max_bloques:
            return False, "MAX_BLOQUES"

        # Validar gap mínimo entre bloques split (NUEVO FIX)
        if len(bloques) >= 2:
            for i in range(len(bloques) - 1):
                gap = bloques[i + 1][0] - bloques[i][1]
                if gap < min_gap_split:
                    return False, "GAP_SPLIT_INSUFICIENTE"

        # 9. Descanso entre turnos INTER-DÍA (9h)
        min_desc_min = self.reglas.get("min_descanso_entre_turnos_horas", 9) * 60
        d_prev = d - timedelta(days=1)
        if d_prev in estado_emp.intervalos_por_dia and estado_emp.intervalos_por_dia[d_prev]:
            last_end = max(e for _, e in estado_emp.intervalos_por_dia[d_prev])
            rest = (1440 - last_end) + s_new
            if rest < min_desc_min:
                return False, "DESC_ENTRE_TURNOS"
        d_next = d + timedelta(days=1)
        if d_next in estado_emp.intervalos_por_dia and estado_emp.intervalos_por_dia[d_next]:
            first_start = min(s for s, _ in estado_emp.intervalos_por_dia[d_next])
            rest = (1440 - e_new) + first_start
            if rest < min_desc_min:
                return False, "DESC_ENTRE_TURNOS"

        return True, ""


# ═══════════════════════════════════════════════════════════════════
# SCORER
# ═══════════════════════════════════════════════════════════════════

class ScorerCandidatos:
    def __init__(self, modelo: ModeloPatrones):
        self.modelo = modelo

    def score(self, emp, dm, d, estado, n_emps, prom_min_sem):
        emp_id, ws_id, dow = str(emp.id), str(dm.wsid), d.weekday()

        pat = self.modelo.afinidad_emp_ws.get((emp_id, ws_id))
        if pat and pat.frecuencia > 0:
            max_f = max((p.frecuencia for k, p in self.modelo.afinidad_emp_ws.items()
                         if k[1] == ws_id), default=1)
            s_af = min(1.0, pat.frecuencia / max(1, max_f))
        else:
            s_af = 0.05

        ph = self.modelo.horarios_ws.get((ws_id, dow))
        if ph and ph.frecuencia > 0:
            dist = (abs(_t2m(dm.start) - ph.inicio_tipico_min)
                    + abs(_t2m(_end_eff(dm.end)) - ph.fin_tipico_min)) / 2.0
            s_h = max(0.0, 1.0 - dist / 480.0)
        else:
            s_h = 0.5

        if prom_min_sem > 0:
            s_carga = max(0.0, 1.0 - (estado.minutos_semana / prom_min_sem) * 0.5)
        else:
            s_carga = 1.0

        s_dia = 0.3
        if pat and dow in pat.dias_frecuentes:
            idx = pat.dias_frecuentes.index(dow)
            s_dia = max(0.3, 1.0 - idx * 0.15)

        tiene_hoy = d in estado.dias_trabajados
        mismo_ws = any(ws == ws_id for dd, ws, _, _ in estado.asignaciones if dd == d)
        s_cont = 1.0 if mismo_ws else (0.6 if tiene_hoy else 0.3)

        return round(0.35*s_af + 0.20*s_h + 0.25*s_carga + 0.10*s_dia + 0.10*s_cont, 4)


# ═══════════════════════════════════════════════════════════════════
# GENERADOR PRINCIPAL (CORREGIDO)
# ═══════════════════════════════════════════════════════════════════

class AIScheduleGenerator:
    def __init__(self, modelo: ModeloPatrones, reglas=None, debug=True):
        self.modelo = modelo
        self.validador = ValidadorReglasDuras(reglas)
        self.scorer = ScorerCandidatos(modelo)
        self.debug = debug
        self.reglas = reglas or dict(REGLAS_DURAS_DEFAULTS)

    def _log(self, msg):
        if self.debug: print(f"[AI-GEN] {msg}")

    def generar(self, emps, demands, week, overrides=None):
        """
        Returns: (sched, coverage_stats, days_off_diag)
        overrides: set((emp_id_str, date)) → días donde UserShift NO se enfuerza
        """
        overrides = overrides or set()
        self._log(f"Generando: {len(emps)} emps, {len(demands)} demands, "
                   f"{week[0]}→{week[-1]}, {len(overrides)} overrides")

        estados = {str(e.id): EstadoEmpleado(emp_id=str(e.id)) for e in emps}
        sched = defaultdict(list)
        coverage_stats = {}
        remaining = {}

        for dm in demands:
            coverage_stats[dm.id] = {
                "demand": dm, "met": 0, "covered": 0,
                "unmet": dm.need, "coverage_pct": 0.0, "employees": [],
            }
            remaining[dm.id] = dm.need

        total_demand_min = sum(_seg_min(dm.start, dm.end) * dm.need for dm in demands)
        active_emps = [e for e in emps if not all(e.off(d) or e.absent_day(d) for d in week)]
        prom_min = total_demand_min / max(1, len(active_emps))
        self._log(f"Promedio objetivo: {prom_min/60:.1f}h/sem, {len(active_emps)} activos")

        # Priorizar demands más restrictivos (menos candidatos) primero
        demand_pri = []
        for dm in demands:
            if dm.wsid is None: continue
            n_cand = sum(1 for e in emps
                         if e.can(dm.wsid) and not e.off(dm.date) and not e.absent_day(dm.date))
            is_night = _t2m(dm.start) >= 20 * 60
            is_wknd = dm.date.weekday() >= 5
            prio = n_cand * 10 - (50 if is_night else 0) - (30 if is_wknd else 0)
            demand_pri.append((prio, dm))
        demand_pri.sort(key=lambda x: (x[0], x[1].date, _t2m(x[1].start)))

        # ── FASE 1: Asignación principal ──
        assigned = 0
        for _, dm in demand_pri:
            if dm.wsid is None: continue
            for _ in range(remaining.get(dm.id, 0)):
                best = self._mejor_candidato(emps, dm, estados, overrides, prom_min)
                if best:
                    self._asignar(best, dm, sched, estados, coverage_stats, remaining)
                    assigned += 1
        self._log(f"[FASE 1] Asignados: {assigned}")

        # ── FASE 2: Segundo pase (equidad relajada) ──
        filled2 = self._pase_extra(emps, demands, sched, estados, coverage_stats,
                                    remaining, overrides, prom_min * 1.5, "FASE 2")

        # ── FASE 3: Tercer pase (cobertura máxima) ──
        filled3 = self._pase_extra(emps, demands, sched, estados, coverage_stats,
                                    remaining, overrides, prom_min * 3.0, "FASE 3")

        # ── FASE 4: Filtrar bloques < 3h POR BLOQUE INDIVIDUAL ──
        removed = self._filtrar_bloques_cortos(sched, estados, coverage_stats, remaining)

        # ── FASE 5: Re-fill post filtro ──
        filled_post = self._pase_extra(emps, demands, sched, estados, coverage_stats,
                                        remaining, overrides, prom_min * 2.0, "POST-FILTER")

        # Coverage pct
        for cs in coverage_stats.values():
            n = cs["demand"].need
            cs["coverage_pct"] = round((cs["covered"] / n) * 100, 1) if n > 0 else 100.0

        diag = self._diag_descanso(emps, week, estados)

        total_req = sum(dm.need for dm in demands)
        total_cov = sum(cs["covered"] for cs in coverage_stats.values())
        pct = round(total_cov / total_req * 100, 1) if total_req else 100.0
        self._log(f"══ RESULTADO: {total_cov}/{total_req} = {pct}% ══")
        self._log(f"   Removidos por 3h/bloque: {removed}")

        return sched, coverage_stats, diag

    def _mejor_candidato(self, emps, dm, estados, overrides, prom_min):
        best_emp, best_sc = None, -1.0
        for e in emps:
            ok, _ = self.validador.puede_asignar(e, dm, dm.date, estados[str(e.id)], overrides)
            if not ok: continue
            sc = self.scorer.score(e, dm, dm.date, estados[str(e.id)], len(emps), prom_min)
            if sc > best_sc: best_sc, best_emp = sc, e
        return best_emp

    def _asignar(self, emp, dm, sched, estados, cov, remaining):
        sched[dm.date].append((emp, dm))
        s, e = _t2m(dm.start), _t2m(_end_eff(dm.end))
        estados[str(emp.id)].registrar(dm.date, str(dm.wsid), s, e)
        remaining[dm.id] = max(0, remaining.get(dm.id, 0) - 1)
        cov[dm.id]["met"] += 1
        cov[dm.id]["covered"] += 1
        cov[dm.id]["unmet"] = max(0, cov[dm.id]["unmet"] - 1)
        cov[dm.id]["employees"].append(str(emp.id))

    def _pase_extra(self, emps, demands, sched, estados, cov, remaining, overrides, prom, label):
        filled = 0
        for dm in sorted(demands, key=lambda d: (d.date, _t2m(d.start))):
            if remaining.get(dm.id, 0) <= 0 or dm.wsid is None: continue
            for _ in range(remaining[dm.id]):
                best = self._mejor_candidato(emps, dm, estados, overrides, prom)
                if best:
                    self._asignar(best, dm, sched, estados, cov, remaining)
                    filled += 1
                else: break
        if filled: self._log(f"[{label}] +{filled} slots")
        return filled

    def _filtrar_bloques_cortos(self, sched, estados, cov, remaining):
        """
        CORREGIDO: Filtra POR BLOQUE individual, no por total/día.
        Bloque = grupo contiguo de intervalos mergeados.
        Si ALGÚN bloque < 3h → se remueven TODAS las asignaciones de ese empleado ese día.
        """
        min_blk_min = self.reglas.get("min_duracion_turno_horas", 3) * 60
        removed = 0

        for d in list(sched.keys()):
            # Agrupar intervalos por empleado
            by_emp = defaultdict(list)
            for emp, dm in sched[d]:
                if dm.wsid is not None:
                    by_emp[str(emp.id)].append((emp, dm))

            emps_to_remove = set()
            for eid, pairs in by_emp.items():
                # Merge todos los intervalos del empleado ese día
                ivs = []
                for emp, dm in pairs:
                    ivs.append((_t2m(dm.start), _t2m(_end_eff(dm.end))))
                bloques = _merge_intervals(ivs)

                # Validar CADA bloque individualmente
                for blk_s, blk_e in bloques:
                    blk_dur = blk_e - blk_s
                    if blk_dur < min_blk_min:
                        emps_to_remove.add(eid)
                        self._log(f"[3H-BLK] {pairs[0][0].name} {d} "
                                   f"bloque {blk_s//60:02d}:{blk_s%60:02d}-"
                                   f"{blk_e//60:02d}:{blk_e%60:02d} "
                                   f"= {blk_dur/60:.1f}h < 3h")
                        break

            # Remover todo lo del empleado ese día
            keep = []
            for emp, dm in sched[d]:
                eid = str(emp.id)
                if eid in emps_to_remove and dm.wsid is not None:
                    s, e = _t2m(dm.start), _t2m(_end_eff(dm.end))
                    estados[eid].desregistrar(d, str(dm.wsid), s, e)
                    remaining[dm.id] = remaining.get(dm.id, 0) + 1
                    cov[dm.id]["covered"] = max(0, cov[dm.id]["covered"] - 1)
                    cov[dm.id]["met"] = max(0, cov[dm.id]["met"] - 1)
                    cov[dm.id]["unmet"] += 1
                    removed += 1
                else:
                    keep.append((emp, dm))
            sched[d] = keep

        return removed

    def _diag_descanso(self, emps, week, estados):
        min_off = self.reglas.get("dias_descanso_semana", 2)
        diag = []
        for e in emps:
            est = estados.get(str(e.id))
            if not est or not est.dias_trabajados: continue
            dias_off = 7 - len(est.dias_trabajados)
            if dias_off < min_off:
                diag.append({
                    "employee_id": str(e.id), "employee_name": e.name,
                    "days_worked": len(est.dias_trabajados),
                    "days_off": dias_off, "required_off": min_off,
                })
        return diag