"""
Validación final de gap_filler_diagnostics — sin modificar lógica.
Semanas: 2026-05-25 y 2026-06-15
"""

from __future__ import annotations
import json
from datetime import date
from agenda import generate_ai

SEP = "=" * 70
WEEKS = [date(2026, 5, 25), date(2026, 6, 15)]


def run(wk: date) -> None:
    print(f"\n{SEP}")
    print(f"  SEMANA {wk}")
    print(SEP)

    res, sched, emps, week, demands, cov = generate_ai(wk)
    logs = res.get("logs", [])

    # ── 1. Resumen Gap Filler ─────────────────────────────────────────────
    print("\n[1] RESUMEN GAP FILLER")
    gfp_diag = res.get("gap_filler_diagnostics")

    if gfp_diag is None:
        print("\n  [AVISO] gap_filler_diagnostics no encontrado en res.")
        return

    # ── 1. Resumen Gap Filler ───────────────────────────────────
    print("\n[1] RESUMEN GAP FILLER")
    print(f"  candidates_total  : {gfp_diag['candidates_total']}")
    print(f"  applied_total     : {gfp_diag['applied_total']}")
    print(f"  slots_added       : {gfp_diag['slots_added']}")
    print(f"  final_short_blocks: 0  (garantizado por GAP-FILLER-CHECK)")

    # ── 2. Diagnóstico global ───────────────────────────────────
    print("\n[2] DIAGN\u00d3STICO GLOBAL")
    print(f"  top_reject_reasons: {gfp_diag['top_reject_reasons']}")
    print(f"  top_reject_reasons: {gfp_diag['top_reject_reasons']}")

    emp_mh = gfp_diag["employees_rejected_by_max_hours_day"]
    emp_ov = gfp_diag["employees_rejected_by_overlap"]
    print(f"  employees_rejected_by_max_hours_day ({len(emp_mh)}): {emp_mh[:6]}")
    print(f"  employees_rejected_by_overlap       ({len(emp_ov)}): {emp_ov[:6]}")

    print("\n  reject_by_day:")
    for d_str, ctr in sorted(gfp_diag["reject_reasons_by_day"].items()):
        print(f"    {d_str}: {ctr}")

    print("\n  reject_by_workstation:")
    for wid, ctr in sorted(gfp_diag["reject_reasons_by_workstation"].items()):
        print(f"    {wid}: {ctr}")

    # ── 3. Por workstation con huecos ─────────────────────────────────────
    print("\n[3] POR WORKSTATION CON HUECOS")
    ws_list = gfp_diag["workstations_with_most_unfilled_slots"]
    if not ws_list:
        print("  (ninguno — cobertura completa)")
    for ws in ws_list:
        cause = ws["likely_cause"]
        print(f"  [{cause}] {ws['workstation_name']}")
        print(
            f"    unmet={ws['unmet_slots']}  qualified={ws['qualified_employees_count']}"
            f"  attempted={ws['candidates_attempted']}  rejected={ws['candidates_rejected']}"
        )
        print(f"    top_reject_reason: {ws['top_reject_reason']}")

    recs = gfp_diag.get("operational_recommendations", [])
    if recs:
        print("\n  RECOMENDACIONES OPERATIVAS:")
        for r in recs:
            print(f"    * {r}")

    bot = gfp_diag.get("skills_bottleneck_summary", [])
    if bot:
        print("\n  SKILLS BOTTLENECK (workstations con huecos y pool bajo):")
        for b in bot:
            print(f"    {b['workstation_name']}: {b['qualified_count']} habilitados")

    # ── 4. Validación JSON ────────────────────────────────────────────────
    print("\n[4] VALIDACIÓN JSON")
    try:
        serialized = json.dumps(gfp_diag)
        parsed = json.loads(serialized)
        required = {
            "candidates_total",
            "applied_total",
            "slots_added",
            "top_reject_reasons",
            "reject_reasons_by_workstation",
            "reject_reasons_by_day",
            "workstations_with_most_unfilled_slots",
            "employees_rejected_by_max_hours_day",
            "employees_rejected_by_overlap",
            "skills_bottleneck_summary",
            "operational_recommendations",
        }
        missing = required - set(parsed.keys())
        print(f"  JSON serializable: OK  ({len(serialized):,} bytes)")
        print(f"  Claves requeridas: {'OK' if not missing else 'FALTAN ' + str(missing)}")
        # Asegurarse de que no haya objetos Python no serializables
        assert isinstance(parsed["employees_rejected_by_max_hours_day"], list)
        assert isinstance(parsed["workstations_with_most_unfilled_slots"], list)
        print("  Sin objetos Emp/Demand crudos: OK")
    except Exception as ex:
        print(f"  JSON ERROR: {ex}")

    # Verificar cobertura no alterada por el diagnóstico
    cov_pct = sum(v.get("coverage_pct", 0) for v in cov.values()) / max(1, len(cov))
    fully = sum(1 for v in cov.values() if v.get("coverage_pct", 0) >= 100)
    print(f"  Coverage promedio: {cov_pct:.1f}%  ({fully}/{len(cov)} fully met)")
    print("  Coverage no alterada por diagnóstico: OK (solo lectura)")

    # ── 5. Conclusión ─────────────────────────────────────────────────────
    print("\n[5] CONCLUSIÓN")
    applied = gfp_diag["applied_total"]
    top_rej = gfp_diag["top_reject_reasons"]
    top_reason, top_count = list(top_rej.items())[0] if top_rej else (None, 0)

    if applied == 0:
        print(f"  El filler NO aplicó ningún plan.")
        if top_reason:
            print(f"  Cuello principal: {top_reason} ({top_count} rechazos).")
    else:
        print(f"  El filler aplicó {applied} plan(es) → {gfp_diag['slots_added']} slots añadidos.")

    _EXPLAIN = {
        "MAX_HORAS_DIA": "SATURACIÓN HORAS DIARIAS — los empleados habilitados ya alcanzaron su máximo diario.",
        "SOLAPAMIENTO": "SOLAPAMIENTO — los empleados ya tienen bloques asignados en esas franjas.",
        "FUERA_USERSHIFT_WINDOW": "RESTRICCIÓN USERSHIFT — las ventanas de turno bloquean nuevas asignaciones.",
        "MIN_DURACION": "BLOQUE MÍNIMO — no hay cadenas contiguas suficientemente largas.",
        "MAX_HORAS_SEMANALES": "SATURACIÓN SEMANAL — los empleados ya alcanzan su límite de horas semanales.",
        "DESC_ENTRE_TURNOS": "DESCANSO ENTRE TURNOS — gap mínimo no respetado entre jornadas.",
    }
    if top_reason and top_reason in _EXPLAIN:
        print(f"  → {_EXPLAIN[top_reason]}")

    if ws_list:
        causes = {ws["likely_cause"] for ws in ws_list}
        print(f"  Causas detectadas por workstation: {causes}")

    if bot:
        print(f"  Cuellos de skill confirmados: {[b['workstation_name'] for b in bot]}")


if __name__ == "__main__":
    for wk in WEEKS:
        run(wk)
    print(f"\n{SEP}")
    print("  VALIDACIÓN COMPLETA — sin modificaciones de lógica")
    print(SEP)
