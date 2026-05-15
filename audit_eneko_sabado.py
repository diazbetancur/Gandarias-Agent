"""
audit_eneko_sabado.py
=====================
Auditoría puntual: ¿Por qué Eneko no fue asignado el sábado 2026-06-20?

Semana  : 2026-06-15
Empleado: aa8c32e8-6189-41b6-b933-363629670c98  ENEKO SARASOLA USANDIZAGA
Día     : 2026-06-20 (sábado)
WS      : ENLACE (huecos reales: 12:00-13, 13:00-14, 19:00-23, 23:00-00)

Pasos:
 1. Cargar perfil desde BD (load_data)
 2. Calcular estado antes del sábado (replay de asignaciones conocidas)
 3. Evaluar cada hueco con _validate_chain_for_employee
 4. Auditar si fue candidato en cada fase (Gen / GapFiller / Repair)
 5. Entregar reporte estructurado
"""
from __future__ import annotations

import os
import sys
from collections import defaultdict
from datetime import date, time, timedelta
from pprint import pformat

ROOT = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, ROOT)

from agenda import load_data, plan_usershift_day_modes, build_hybrid_groups
from services.ai_scheduler import (
    AIScheduleGenerator,
    EstadoEmpleado,
    ModeloPatrones,
    REGLAS_DURAS_DEFAULTS,
    _t2m, _end_min, _seg_min, _merge_intervals, _has_overlap,
)

ENEKO_ID   = "aa8c32e8-6189-41b6-b933-363629670c98"
WEEK_START = date(2026, 6, 15)
SABADO     = date(2026, 6, 20)
VIERNES    = date(2026, 6, 19)

# Asignaciones conocidas de Eneko antes del sábado (de la respuesta observada)
KNOWN_ASSIGNMENTS = [
    # (date, start_time, end_time, wsname)
    (date(2026, 6, 17), time(20, 0),  time(23, 59), "PARRILLERO"),
    (date(2026, 6, 18), time(20, 30), time(22, 0),  "ENLACE"),
    (date(2026, 6, 18), time(22, 0),  time(0, 0),   "ENLACE"),
    (date(2026, 6, 19), time(16, 0),  time(19, 0),  "PARRILLERO"),
    (date(2026, 6, 19), time(19, 0),  time(0, 0),   "ENLACE"),
]

SEP = "─" * 70


def _fmt_t(t: time) -> str:
    return t.strftime("%H:%M")


def _min_to_hm(m: int) -> str:
    return f"{m//60}h{m%60:02d}m"


def main() -> None:
    print("=" * 70)
    print("  AUDITORÍA ENEKO SARASOLA — SÁBADO 2026-06-20")
    print("=" * 70)

    # ── Cargar datos reales ─────────────────────────────────────────────────
    print("\n[CARGANDO DATOS DESDE BD...]")
    emps, demands, (tpl_id, tpl_name), week, shift_types, reglas, hybrid_pairs, _ = load_data(WEEK_START)
    overrides, _ = plan_usershift_day_modes(emps, demands, week)

    min_blk_min   = reglas.get("min_duracion_turno_horas", 3) * 60
    max_h_dia_min = reglas.get("max_horas_por_dia", 9) * 60
    min_rest_min  = reglas.get("min_descanso_entre_turnos_horas", 9) * 60
    min_gap_split = reglas.get("min_gap_split_horas", 3) * 60
    max_dias      = reglas.get("max_dias_trabajo_semana", 5)
    max_bloques   = reglas.get("max_bloques_por_dia", 2)

    print(f"  Reglas cargadas: MAX_H_DIA={max_h_dia_min//60}h  MIN_SHIFT={min_blk_min//60}h  "
          f"MIN_REST={min_rest_min//60}h  MIN_SPLIT_GAP={min_gap_split//60}h  "
          f"MAX_DIAS={max_dias}  MAX_BLOQUES={max_bloques}")

    # ── Localizar a Eneko ───────────────────────────────────────────────────
    eneko = next((e for e in emps if str(e.id) == ENEKO_ID), None)
    if eneko is None:
        print(f"\n  [ERROR] Eneko no encontrado (id={ENEKO_ID}). Verificar BD.")
        return
    print(f"\n  Empleado encontrado: {eneko.name}  (id={eneko.id})")

    # ── SECCIÓN 1: Perfil ───────────────────────────────────────────────────
    print(f"\n{SEP}")
    print("[1] PERFIL DE ENEKO")
    print(SEP)

    # Skills / workstations
    ws_ids_habilitados = {str(dm.wsid): dm.wsname for dm in demands if eneko.can(dm.wsid) and dm.wsid is not None}
    print(f"  Workstations con skill: {list(ws_ids_habilitados.values())}")

    # ENLACE ws_id
    enlace_ws_id = next((str(dm.wsid) for dm in demands if dm.wsname.strip().upper() == "ENLACE"), None)
    print(f"  ENLACE ws_id: {enlace_ws_id}")
    can_enlace = eneko.can(enlace_ws_id) if enlace_ws_id else False
    print(f"  can(ENLACE): {can_enlace}")

    # Disponibilidad sábado
    print(f"\n  --- Disponibilidad sábado ({SABADO}) ---")
    off_sabado     = eneko.off(SABADO)
    absent_sabado  = eneko.absent_day(SABADO)
    print(f"  off({SABADO})       : {off_sabado}")
    print(f"  absent_day({SABADO}): {absent_sabado}")

    # Disponibilidad por franja
    test_slots = [
        (time(12, 0), time(13, 0)),
        (time(13, 0), time(14, 0)),
        (time(19, 0), time(23, 0)),
        (time(23, 0), time(0, 0)),
    ]
    print(f"  available(SABADO, franja):")
    for s, e in test_slots:
        av = eneko.available(SABADO, s, e)
        print(f"    {_fmt_t(s)}-{_fmt_t(e)}: {av}")

    # UserShift sábado
    dow_sabado = SABADO.weekday()   # 5 = sábado
    us_wins = getattr(eneko, "user_shift_windows", {}).get(dow_sabado, [])
    override_pair = (str(eneko.id), SABADO)
    is_override = override_pair in overrides
    print(f"\n  UserShift windows (dow={dow_sabado}): {us_wins}")
    print(f"  override en sábado: {is_override}")

    generator = AIScheduleGenerator(modelo=ModeloPatrones(), reglas=reglas, debug=False)
    print(f"\n  _usershift_ok por franja:")
    for s, e in test_slots:
        ok = generator.validador._usershift_ok(eneko, SABADO, s, e, overrides)
        print(f"    {_fmt_t(s)}-{_fmt_t(e)}: {ok}")

    # Límite semanal
    limit_fn = getattr(eneko, "weekly_hours_limit", None)
    weekly_limit = limit_fn() if callable(limit_fn) else None
    print(f"\n  weekly_hours_limit: {weekly_limit} min  ({(weekly_limit or 0)//60}h)")

    # ── SECCIÓN 2: Estado antes del sábado ─────────────────────────────────
    print(f"\n{SEP}")
    print("[2] ESTADO DE ENEKO ANTES DEL SÁBADO")
    print(SEP)

    estado = EstadoEmpleado(emp_id=str(eneko.id))

    # Encontrar objetos demand para las asignaciones conocidas
    def _find_demand(d: date, ws: str, s: time, e: time):
        for dm in demands:
            if (dm.date == d
                    and dm.wsname.strip().upper() == ws.upper()
                    and dm.start == s
                    and dm.end == e):
                return dm
        return None

    def _register_fake(estado: EstadoEmpleado, d: date, ws_id: str, s: time, e: time):
        s_min = _t2m(s)
        e_min = _end_min(e)
        dur   = _seg_min(s, e)
        estado.minutos_semana += dur
        estado.minutos_por_dia[d] = estado.minutos_por_dia.get(d, 0) + dur
        estado.dias_trabajados.add(d)
        estado.intervalos_por_dia.setdefault(d, []).append((s_min, e_min))
        estado.asignaciones.append((d, str(ws_id), s_min, e_min))

    print("  Replay de asignaciones conocidas:")
    for (d, s, e, ws) in KNOWN_ASSIGNMENTS:
        dur = _seg_min(s, e)
        ws_id = next((str(dm.wsid) for dm in demands
                      if dm.wsname.strip().upper() == ws.upper()), "?")
        _register_fake(estado, d, ws_id, s, e)
        print(f"    {d}  {_fmt_t(s)}-{_fmt_t(e)}  {ws}  ({_min_to_hm(dur)})")

    print(f"\n  horas_semana antes del sábado  : {_min_to_hm(estado.minutos_semana)}")
    print(f"  días_trabajados antes del sábado: {sorted(estado.dias_trabajados)}")
    print(f"  horas sábado actuales           : {_min_to_hm(estado.minutos_por_dia.get(SABADO, 0))}")
    print(f"  bloques sábado actuales         : {estado.intervalos_por_dia.get(SABADO, [])}")

    # Descanso viernes → sábado
    ivs_viernes = estado.intervalos_por_dia.get(VIERNES, [])
    last_viernes = max(e for _, e in ivs_viernes) if ivs_viernes else None
    print(f"\n  Última salida viernes           : {last_viernes} min ({_min_to_hm(last_viernes) if last_viernes else 'N/A'})")
    if last_viernes is not None:
        for s, e in test_slots:
            first_sab = _t2m(s)
            rest = (1440 - last_viernes) + first_sab
            print(f"  Descanso viernes→sáb {_fmt_t(s)}: {rest} min ({_min_to_hm(rest)})  >= {_min_to_hm(min_rest_min)}? {rest >= min_rest_min}")

    # ── SECCIÓN 3: Validación manual de cada demanda ────────────────────────
    print(f"\n{SEP}")
    print("[3] VALIDACIÓN MANUAL DE CADA HUECO ENLACE DEL SÁBADO")
    print(SEP)

    # Demandas ENLACE del sábado
    enlace_sabado = [
        dm for dm in demands
        if dm.date == SABADO
        and dm.wsname.strip().upper() == "ENLACE"
        and dm.wsid is not None
    ]
    enlace_sabado.sort(key=lambda dm: _t2m(dm.start))

    print(f"  Demandas ENLACE sábado ({len(enlace_sabado)}):")
    for dm in enlace_sabado:
        print(f"    {_fmt_t(dm.start)}-{_fmt_t(dm.end)}  id={dm.id}  need={dm.need}")

    print()
    target_slots = [
        (time(12, 0), time(13, 0)),
        (time(13, 0), time(14, 0)),
        (time(19, 0), time(23, 0)),
        (time(23, 0), time(0, 0)),
    ]

    # Para validación de chain usamos el validador del generator
    traces = []
    for t_s, t_e in target_slots:
        chain = [dm for dm in enlace_sabado if dm.start == t_s and dm.end == t_e]
        if not chain:
            print(f"  [{_fmt_t(t_s)}-{_fmt_t(t_e)}] — demanda no encontrada en carga de datos")
            traces.append({"slot": f"{_fmt_t(t_s)}-{_fmt_t(t_e)}", "found": False})
            continue

        dm = chain[0]
        dur = _seg_min(dm.start, dm.end)

        # Validación paso a paso (replicar _validate_chain_for_employee manualmente)
        result = {
            "slot": f"{_fmt_t(t_s)}-{_fmt_t(t_e)}",
            "demand_id": dm.id,
            "demanded": dm.need,
            "found": True,
            "dur_min": dur,
        }

        steps = []

        # off / absent
        if eneko.off(SABADO):
            result["validation_ok"] = False; result["rejection_reason"] = "DIA_LIBRE"; traces.append(result); steps.append("FAIL: DIA_LIBRE"); continue
        if eneko.absent_day(SABADO):
            result["validation_ok"] = False; result["rejection_reason"] = "AUSENCIA"; traces.append(result); steps.append("FAIL: AUSENCIA"); continue

        # max_dias
        if SABADO not in estado.dias_trabajados and len(estado.dias_trabajados) >= max_dias:
            result["validation_ok"] = False; result["rejection_reason"] = "MAX_DIAS"; traces.append(result); steps.append("FAIL: MAX_DIAS"); continue

        # skill
        if not eneko.can(dm.wsid):
            result["validation_ok"] = False; result["rejection_reason"] = "SIN_SKILL"; traces.append(result); steps.append("FAIL: SIN_SKILL"); continue

        # available
        if not eneko.available(SABADO, dm.start, dm.end):
            result["validation_ok"] = False; result["rejection_reason"] = "FUERA_VENTANA"; traces.append(result); steps.append("FAIL: FUERA_VENTANA"); continue

        # usershift
        if not generator.validador._usershift_ok(eneko, SABADO, dm.start, dm.end, overrides):
            result["validation_ok"] = False; result["rejection_reason"] = "FUERA_USERSHIFT_WINDOW"; traces.append(result); steps.append("FAIL: FUERA_USERSHIFT"); continue

        # max_horas_dia
        daily_actual = estado.minutos_por_dia.get(SABADO, 0)
        if daily_actual + dur > max_h_dia_min:
            result["validation_ok"] = False; result["rejection_reason"] = "MAX_HORAS_DIA"
            result["daily_before"] = daily_actual; result["daily_after"] = daily_actual + dur; result["limit"] = max_h_dia_min
            traces.append(result); steps.append("FAIL: MAX_HORAS_DIA"); continue

        # max_horas_semanales
        if not generator.validador._weekly_hours_ok(eneko, estado, dur):
            result["validation_ok"] = False; result["rejection_reason"] = "MAX_HORAS_SEMANALES"
            traces.append(result); steps.append("FAIL: MAX_HORAS_SEMANALES"); continue

        # solapamiento
        existing_ivs = list(estado.intervalos_por_dia.get(SABADO, []))
        s_c = _t2m(dm.start); e_c = _end_min(dm.end)
        if _has_overlap(existing_ivs, s_c, e_c):
            result["validation_ok"] = False; result["rejection_reason"] = "SOLAPAMIENTO"; traces.append(result); steps.append("FAIL: SOLAPAMIENTO"); continue

        # merge y checks de bloque
        merged = _merge_intervals(existing_ivs + [(s_c, e_c)])
        if len(merged) > max_bloques:
            result["validation_ok"] = False; result["rejection_reason"] = "MAX_BLOQUES"; traces.append(result); steps.append("FAIL: MAX_BLOQUES"); continue

        bloque_corto = False
        for bs, be in merged:
            if (be - bs) < min_blk_min:
                bloque_corto = True; break
        if bloque_corto:
            result["validation_ok"] = False; result["rejection_reason"] = "BLOQUE_CORTO_FINAL"; traces.append(result); steps.append("FAIL: BLOQUE_CORTO_FINAL"); continue

        gap_fail = False
        for i in range(len(merged) - 1):
            if (merged[i+1][0] - merged[i][1]) < min_gap_split:
                gap_fail = True; break
        if gap_fail:
            result["validation_ok"] = False; result["rejection_reason"] = "GAP_SPLIT_INSUFICIENTE"; traces.append(result); steps.append("FAIL: GAP_SPLIT"); continue

        # descanso viernes→sábado
        if last_viernes is not None:
            first_today = merged[0][0]
            rest = (1440 - last_viernes) + first_today
            if rest < min_rest_min:
                result["validation_ok"] = False; result["rejection_reason"] = "DESC_ENTRE_TURNOS"
                result["rest_min"] = rest; result["min_rest_min"] = min_rest_min
                traces.append(result); steps.append("FAIL: DESC_ENTRE_TURNOS"); continue

        # Si llegamos aquí → VALID
        result["validation_ok"] = True
        result["rejection_reason"] = None
        result["resulting_day_minutes"] = daily_actual + dur
        result["resulting_week_minutes"] = estado.minutos_semana + dur
        result["resulting_blocks"] = merged
        result["merged_block_count"] = len(merged)
        traces.append(result)
        steps.append("PASS")

        print(f"  [{result['slot']}] {steps[-1]} — "
              f"day={_min_to_hm(result['resulting_day_minutes'])}  "
              f"week={_min_to_hm(result['resulting_week_minutes'])}  "
              f"blocks={merged}")
        continue

    # Imprimir los rechazos
    for r in traces:
        if not r.get("validation_ok"):
            print(f"  [{r['slot']}] RECHAZADO — reason={r.get('rejection_reason')}  "
                  + (f"daily={_min_to_hm(r.get('daily_before',0))}/{_min_to_hm(r.get('limit',0))} + {_min_to_hm(r.get('dur_min',0))}" if "daily_before" in r else "")
                  + (f"  rest={_min_to_hm(r.get('rest_min',0))} < {_min_to_hm(r.get('min_rest_min',0))}" if "rest_min" in r else ""))

    # ── SECCIÓN 3b: Cadena combinada 19:00→00:00 ───────────────────────────
    print(f"\n  --- Cadena combinada 19:00-23:00 + 23:00-00:00 ---")
    chain_19_24 = [dm for dm in enlace_sabado if _t2m(dm.start) >= 19*60]
    chain_19_24.sort(key=lambda dm: _t2m(dm.start))
    if len(chain_19_24) >= 2:
        ok, reason = generator._validate_chain_for_employee(
            eneko, chain_19_24, SABADO, estado, overrides, min_blk_min
        )
        dur_chain = sum(_seg_min(dm.start, dm.end) for dm in chain_19_24)
        print(f"  _validate_chain_for_employee(19:00→00:00): ok={ok}  reason={reason!r}  dur={_min_to_hm(dur_chain)}")
    else:
        print("  No se encontraron ambas demandas para cadena combinada")

    # ── SECCIÓN 4: Auditoría de candidatos del generador (fase base) ────────
    print(f"\n{SEP}")
    print("[4] AUDITORÍA DE CANDIDATOS EN GENERACIÓN BASE (fases 1-3)")
    print(SEP)
    print("  (Esta fase usa el scorer estocástico, no podemos replicar 100% sin re-generar)")
    print("  Verificando si Eneko pasa los filtros previos al scorer:")
    for dm in sorted(enlace_sabado, key=lambda x: _t2m(x.start)):
        if dm.start not in [time(19,0), time(23,0)]:
            continue
        can  = eneko.can(dm.wsid)
        off  = eneko.off(SABADO)
        avail = eneko.available(SABADO, dm.start, dm.end)
        us_ok = generator.validador._usershift_ok(eneko, SABADO, dm.start, dm.end, overrides)
        print(f"  {_fmt_t(dm.start)}-{_fmt_t(dm.end)}: can={can}  off={off}  available={avail}  usershift_ok={us_ok}")

    # ── SECCIÓN 5: Auditoría Gap Filler ────────────────────────────────────
    print(f"\n{SEP}")
    print("[5] AUDITORÍA GAP FILLER (cadena NEW: 19:00→23:00 y 19:00→00:00)")
    print(SEP)
    print("  El GapFiller genera CandidatePlan tipo NEW si Eneko no tiene bloque en sábado.")
    print(f"  Eneko tiene bloque sábado actual: {bool(estado.intervalos_por_dia.get(SABADO))}")
    print(f"  Días trabajados antes de sábado: {sorted(estado.dias_trabajados)}")
    print(f"  ¿Alcanza max_dias ({max_dias}) si añade sábado? {len(estado.dias_trabajados) + (1 if SABADO not in estado.dias_trabajados else 0)} días")

    for t_s, t_e in [(time(19,0), time(23,0)), (time(23,0), time(0,0))]:
        chain = [dm for dm in enlace_sabado if dm.start == t_s and dm.end == t_e]
        if not chain:
            print(f"  [{_fmt_t(t_s)}-{_fmt_t(t_e)}] — no encontrada"); continue
        ok, reason = generator._validate_chain_for_employee(
            eneko, chain, SABADO, estado, overrides, min_blk_min
        )
        dur = _seg_min(t_s, t_e)
        print(f"  [{_fmt_t(t_s)}-{_fmt_t(t_e)}]  validate_chain → ok={ok}  reason={reason!r}  dur={_min_to_hm(dur)}")

    # ── SECCIÓN 6: Auditoría RepairEngine ───────────────────────────────────
    print(f"\n{SEP}")
    print("[6] AUDITORÍA REPAIR ENGINE")
    print(SEP)
    print("  El RepairEngine usa _validate_chain_for_employee también.")
    print("  Si la validación en [3] y [5] da ok=True, el Repair también debería aceptarle.")
    print("  La restricción más probable que explica la ausencia en todas las fases:")
    dominant = {}
    for r in traces:
        rej = r.get("rejection_reason")
        if rej:
            dominant[rej] = dominant.get(rej, 0) + 1
    print(f"  Rechazos detectados: {dominant}")

    # ── SECCIÓN 7: Bug coverage_pct ─────────────────────────────────────────
    print(f"\n{SEP}")
    print("[7] BUG coverage_pct")
    print(SEP)
    print("  En coverage_details: demanded=4, covered=1, unmet=3, coverage_pct=0.0")
    print("  Formula: coverage_pct = round(covered/need * 100, 1)")
    print("  Para covered=1, need=4: coverage_pct = round(1/4*100,1) = 25.0")
    print("  Si coverage_pct=0.0 cuando covered>0 → BUG: 'need' puede estar en 0")
    print("  Probable causa: cs['demand'].need se actualiza durante la generación")
    print("  o hay distinción entre 'need' original y 'covered' real.")
    print("  Verificar en _asignar si se decrementa cs['demand'].need incorrectamente.")

    # ── SECCIÓN 8: Reporte final ─────────────────────────────────────────────
    print(f"\n{'='*70}")
    print("[8] REPORTE FINAL: employee_opportunity_trace")
    print("="*70)

    enlace_opportunities = []
    for r in traces:
        if not r.get("found"):
            continue
        entry = {
            "demand_id": r.get("demand_id"),
            "time": r["slot"],
            "validation_ok": r.get("validation_ok"),
            "rejection_reason": r.get("rejection_reason"),
            "was_candidate_generator": "UNKNOWN (requiere re-gen con trazado)",
            "was_candidate_gap_filler": r.get("validation_ok") is True,
            "was_candidate_repair": r.get("validation_ok") is True,
            "candidate_score": "N/A (no re-gen)",
            "resulting_day_minutes": r.get("resulting_day_minutes"),
            "resulting_week_minutes": r.get("resulting_week_minutes"),
            "resulting_blocks": str(r.get("resulting_blocks")),
        }
        enlace_opportunities.append(entry)

    trace = {
        "employee_id": ENEKO_ID,
        "employee_name": eneko.name,
        "saturday_availability": {
            "off": eneko.off(SABADO),
            "absent": eneko.absent_day(SABADO),
            "available_19_23": eneko.available(SABADO, time(19, 0), time(23, 0)),
            "available_23_00": eneko.available(SABADO, time(23, 0), time(0, 0)),
        },
        "saturday_user_shift": {
            "windows": str(us_wins),
            "is_override": is_override,
            "usershift_ok_19_23": generator.validador._usershift_ok(eneko, SABADO, time(19,0), time(23,0), overrides),
            "usershift_ok_23_00": generator.validador._usershift_ok(eneko, SABADO, time(23,0), time(0,0), overrides),
        },
        "saturday_rules": {
            "max_horas_dia": max_h_dia_min,
            "min_blk_min": min_blk_min,
            "min_rest_min": min_rest_min,
            "min_gap_split": min_gap_split,
            "max_dias": max_dias,
            "max_bloques": max_bloques,
            "weekly_limit_min": weekly_limit,
        },
        "assigned_week_minutes": estado.minutos_semana,
        "assigned_days": sorted(str(d) for d in estado.dias_trabajados),
        "friday_last_end_min": last_viernes,
        "saturday_current_blocks": estado.intervalos_por_dia.get(SABADO, []),
        "enlace_opportunities": enlace_opportunities,
        "conclusion": None,
        "suspected_bug_location": None,
    }

    # Determinar conclusión
    all_ok    = [r for r in traces if r.get("found") and r.get("validation_ok")]
    all_fail  = [r for r in traces if r.get("found") and not r.get("validation_ok")]

    print(f"\n  Slots ENLACE sábado evaluados : {len(traces)}")
    print(f"  Válidos según validador        : {len(all_ok)}")
    print(f"  Rechazados según validador     : {len(all_fail)}")

    if all_ok:
        valid_slots = [r["slot"] for r in all_ok]
        trace["conclusion"] = (
            f"D/E — Eneko ES VÁLIDO para {valid_slots} según todas las reglas. "
            f"Si no fue asignado, se perdió por ranking (opción D) "
            f"o ningún plan fue seleccionado (opción E — bug en GapFiller/generador)."
        )
        trace["suspected_bug_location"] = (
            "GapFillingPass o fases 1-3: Eneko superó todas las validaciones pero "
            "no fue seleccionado. Revisar scorer de candidatos y prioridad en GapFiller."
        )
        print(f"\n  CONCLUSIÓN → D o E: Eneko es VÁLIDO para {valid_slots}.")
        print(f"  Si no fue asignado → perdió por ranking (D) o bug en selección (E).")
    elif dominant:
        top_rej = max(dominant, key=dominant.get)
        trace["conclusion"] = (
            f"B — Eneko fue rechazado por regla válida: {top_rej}. "
            f"No hay bug en la lógica, el rechazo es correcto."
        )
        trace["suspected_bug_location"] = f"Ninguno — rechazo por {top_rej} es correcto."
        print(f"\n  CONCLUSIÓN → B: Todos los slots rechazados por {top_rej}.")
    else:
        trace["conclusion"] = "A — Eneko no llegó a ser candidato (filtro previo)."
        trace["suspected_bug_location"] = "Filtro de pre-selección (skill/disponibilidad)."
        print(f"\n  CONCLUSIÓN → A: Filtro previo impidió candidatura.")

    print(f"\n  conclusion              : {trace['conclusion']}")
    print(f"  suspected_bug_location  : {trace['suspected_bug_location']}")
    print()


if __name__ == "__main__":
    main()
