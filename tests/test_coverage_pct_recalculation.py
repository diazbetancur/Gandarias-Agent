# tests/test_coverage_pct_recalculation.py
"""
Pruebas unitarias para recalculate_coverage_percentages() de agenda.py.

Validan que:
  1. coverage_pct se recalcula correctamente tras modificaciones en covered.
  2. El caso concreto covered=1/demanded=4 da 25.0 (no 0.0).
  3. unmet se recomputa como max(demanded - covered, 0).
  4. covered > demanded no produce valores negativos en unmet.
  5. demanded == 0 produce coverage_pct == 100.0 (equivalente a la regla original).
  6. La función es idempotente: llamarla dos veces produce el mismo resultado.
  7. coverage_pct no está obsoleto cuando simulate_repair modifica covered.

NO usa base de datos ni Flask. El único objeto necesario de agenda.py es
recalculate_coverage_percentages().
"""
from __future__ import annotations

import sys
import types
from datetime import date, time
from typing import Any
from unittest.mock import MagicMock

import pytest

# ─────────────────────────────────────────────────────────────────────────────
# Importar recalculate_coverage_percentages aislando dependencias pesadas
# ─────────────────────────────────────────────────────────────────────────────

_HEAVY_MODULES = ["psycopg2", "psycopg2.extensions", "flask", "flask_cors"]


def _load_helper():
    """Importa recalculate_coverage_percentages desde agenda.py."""
    injected = []
    for mod in _HEAVY_MODULES:
        if mod not in sys.modules:
            sys.modules[mod] = MagicMock()
            injected.append(mod)

    try:
        if "agenda" in sys.modules:
            agenda_mod = sys.modules["agenda"]
        else:
            import importlib.util, pathlib

            spec = importlib.util.spec_from_file_location(
                "agenda",
                str(pathlib.Path(__file__).parents[1] / "agenda.py"),
            )
            agenda_mod = importlib.util.module_from_spec(spec)
            sys.modules["agenda"] = agenda_mod
            spec.loader.exec_module(agenda_mod)

        return agenda_mod.recalculate_coverage_percentages
    finally:
        for mod in injected:
            sys.modules.pop(mod, None)


try:
    recalculate_coverage_percentages = _load_helper()
    HELPER_AVAILABLE = True
except Exception as _err:
    HELPER_AVAILABLE = False
    _err_msg = str(_err)

skip_if_unavailable = pytest.mark.skipif(
    not HELPER_AVAILABLE,
    reason=f"recalculate_coverage_percentages no disponible: {'' if HELPER_AVAILABLE else _err_msg}",
)


# ─────────────────────────────────────────────────────────────────────────────
# Fixtures mínimos
# ─────────────────────────────────────────────────────────────────────────────


def _make_demand(need: int = 4, wsname: str = "ENLACE") -> Any:
    """Demand mínimo con atributo .need."""
    dm = types.SimpleNamespace(
        id=f"dm-{wsname}-{need}",
        need=need,
        wsname=wsname,
        date=date(2026, 6, 20),
        start=time(19, 0),
        end=time(23, 0),
        wsid="ws-enlace",
    )
    return dm


def _make_cs(demand, covered: int, unmet: int | None = None, coverage_pct: float = 0.0) -> dict:
    """Coverage-stat mínimo, con coverage_pct potencialmente obsoleto."""
    return {
        "demand": demand,
        "met": covered,
        "covered": covered,
        "unmet": unmet if unmet is not None else max(demand.need - covered, 0),
        "coverage_pct": coverage_pct,
        "employees": [],
    }


# ─────────────────────────────────────────────────────────────────────────────
# Tests
# ─────────────────────────────────────────────────────────────────────────────


@skip_if_unavailable
def test_covered_1_demanded_4_gives_25_pct():
    """Caso concreto del bug: covered=1, demand.need=4 → coverage_pct=25.0."""
    dm = _make_demand(need=4)
    cs_map = {"d1": _make_cs(dm, covered=1, coverage_pct=0.0)}

    recalculate_coverage_percentages(cs_map)

    assert cs_map["d1"]["coverage_pct"] == 25.0


@skip_if_unavailable
def test_coverage_pct_recalculated_after_repair():
    """
    Simula que RepairEngine incrementó covered de 0 a 2 sin tocar coverage_pct.
    recalculate_coverage_percentages debe corregir a 50.0%.
    """
    dm = _make_demand(need=4)
    # Antes del repair: covered=0, pct=0.0
    cs_map = {"d1": _make_cs(dm, covered=0, coverage_pct=0.0)}

    # Simular lo que hace RepairEngine: incrementar covered in-place
    cs_map["d1"]["covered"] = 2
    cs_map["d1"]["unmet"] = 2  # RepairEngine sí actualiza unmet

    # coverage_pct sigue obsoleto = 0.0
    assert cs_map["d1"]["coverage_pct"] == 0.0

    recalculate_coverage_percentages(cs_map)

    assert cs_map["d1"]["coverage_pct"] == 50.0


@skip_if_unavailable
def test_unmet_recalculated_after_covered_changes():
    """
    Simula que Hybrid05 incrementó covered pero dejó unmet sin actualizar.
    recalculate_coverage_percentages debe corregir unmet = max(need - covered, 0).
    """
    dm = _make_demand(need=4)
    # unmet obsoleto = 4 (nunca decrementado), covered = 2
    cs_map = {"d1": _make_cs(dm, covered=2, unmet=4, coverage_pct=0.0)}

    recalculate_coverage_percentages(cs_map)

    assert cs_map["d1"]["unmet"] == 2  # max(4-2, 0)
    assert cs_map["d1"]["coverage_pct"] == 50.0


@skip_if_unavailable
def test_no_stale_coverage_pct_in_response():
    """
    Cuando covered fue modificado por cualquier fase posterior a generar(),
    el resultado final de coverage_pct en cs_map debe ser consistente
    con covered/demand.need, nunca con el valor inicial 0.0.
    """
    scenarios = [
        # (need, covered_final, expected_pct)
        (1, 1, 100.0),
        (2, 1, 50.0),
        (4, 3, 75.0),
        (10, 7, 70.0),
        (3, 0, 0.0),
    ]
    for need, cov, expected in scenarios:
        dm = _make_demand(need=need)
        cs_map = {"d": _make_cs(dm, covered=cov, coverage_pct=-999.0)}  # pct obsoleto
        recalculate_coverage_percentages(cs_map)
        assert cs_map["d"]["coverage_pct"] == expected, (
            f"need={need} covered={cov}: esperaba {expected}, got {cs_map['d']['coverage_pct']}"
        )


@skip_if_unavailable
def test_demanded_zero_gives_100_pct():
    """demanded=0 → coverage_pct=100.0 (ningún slot requerido, vacuamente cubierto)."""
    dm = _make_demand(need=0)
    cs_map = {"d1": _make_cs(dm, covered=0, coverage_pct=0.0)}

    recalculate_coverage_percentages(cs_map)

    assert cs_map["d1"]["coverage_pct"] == 100.0


@skip_if_unavailable
def test_covered_exceeds_demanded_unmet_is_zero():
    """Si covered > need por algún edge-case, unmet debe ser 0 (no negativo)."""
    dm = _make_demand(need=2)
    cs_map = {"d1": _make_cs(dm, covered=3, coverage_pct=0.0)}

    recalculate_coverage_percentages(cs_map)

    assert cs_map["d1"]["unmet"] == 0
    # coverage_pct puede superar 100.0 en este edge-case pero no debe ser negativo
    assert cs_map["d1"]["coverage_pct"] >= 0.0


@skip_if_unavailable
def test_recalculate_is_idempotent():
    """Llamar la función dos veces produce el mismo resultado."""
    dm = _make_demand(need=4)
    cs_map = {"d1": _make_cs(dm, covered=1, coverage_pct=0.0)}

    recalculate_coverage_percentages(cs_map)
    first_pct = cs_map["d1"]["coverage_pct"]
    first_unmet = cs_map["d1"]["unmet"]

    recalculate_coverage_percentages(cs_map)

    assert cs_map["d1"]["coverage_pct"] == first_pct
    assert cs_map["d1"]["unmet"] == first_unmet


@skip_if_unavailable
def test_multiple_demands_all_recalculated():
    """Todos los entries en coverage_stats son recalculados, no solo uno."""
    dm_a = _make_demand(need=2, wsname="ENLACE")
    dm_b = _make_demand(need=3, wsname="PARRILLERO")
    dm_c = _make_demand(need=1, wsname="BARRA")

    cs_map = {
        "a": _make_cs(dm_a, covered=0, coverage_pct=0.0),   # stale 0.0, debe ser 0.0
        "b": _make_cs(dm_b, covered=2, coverage_pct=0.0),   # stale 0.0, debe ser 66.7
        "c": _make_cs(dm_c, covered=1, coverage_pct=0.0),   # stale 0.0, debe ser 100.0
    }

    recalculate_coverage_percentages(cs_map)

    assert cs_map["a"]["coverage_pct"] == 0.0
    assert cs_map["b"]["coverage_pct"] == round(2 / 3 * 100, 1)  # 66.7
    assert cs_map["c"]["coverage_pct"] == 100.0
    assert cs_map["a"]["unmet"] == 2
    assert cs_map["b"]["unmet"] == 1
    assert cs_map["c"]["unmet"] == 0


@skip_if_unavailable
def test_empty_coverage_stats_does_not_raise():
    """coverage_stats vacío no debe lanzar excepción."""
    recalculate_coverage_percentages({})


# ─────────────────────────────────────────────────────────────────────────────
# INTEGRATION TESTS — replica el dict-comprehension de coverage_details en
# generate_ai() para verificar que el JSON nunca contiene pct=0.0/covered>0.
# ─────────────────────────────────────────────────────────────────────────────


def _build_coverage_details(coverage_stats: dict) -> dict:
    """
    Réplica exacta del dict-comprehension de generate_ai():
        "coverage_details": {
            d_id: {
                "demanded": s["demand"].need,
                "covered":  s["covered"],
                "unmet":    s["unmet"],
                "coverage_pct": s["coverage_pct"],
            }
            for d_id, s in coverage_stats.items()
        }
    Permite testear la serialización sin levantar Flask/BD.
    """
    return {
        d_id: {
            "demanded": s["demand"].need,
            "covered": s["covered"],
            "unmet": s["unmet"],
            "coverage_pct": s["coverage_pct"],
        }
        for d_id, s in coverage_stats.items()
    }


def _assert_no_stale_pct(coverage_details: dict) -> None:
    """
    Criterio de corrección global:
      No debe existir ningún entry con covered > 0 AND demanded > 0 AND coverage_pct == 0.0.
    """
    bad = [
        (k, v)
        for k, v in coverage_details.items()
        if v["covered"] > 0 and v["demanded"] > 0 and v["coverage_pct"] == 0.0
    ]
    assert not bad, (
        f"coverage_details tiene {len(bad)} entrada(s) con covered>0/demanded>0/pct=0.0:\n"
        + "\n".join(
            f"  {k}: demanded={v['demanded']} covered={v['covered']} pct={v['coverage_pct']}"
            for k, v in bad
        )
    )


@skip_if_unavailable
def test_build_coverage_details_after_recalc_no_stale():
    """
    Integración: simula la pipeline completa
      generar (stale) → hybrid05 (incrementa covered) → repair (incrementa covered)
      → recalculate → build coverage_details
    Ningún entry del JSON final puede tener covered>0/demanded>0/pct=0.0.
    """
    # Estado inicial como lo deja generar() con pct calculado en fase 1
    dm_a = _make_demand(need=4, wsname="ENLACE")
    dm_b = _make_demand(need=2, wsname="PARRILLERO")
    dm_c = _make_demand(need=1, wsname="BARRA")

    coverage_stats = {
        "a": _make_cs(dm_a, covered=0, coverage_pct=0.0),   # gerado con 0 asignados
        "b": _make_cs(dm_b, covered=2, coverage_pct=100.0), # completamente cubierto
        "c": _make_cs(dm_c, covered=0, coverage_pct=0.0),   # sin cubrir
    }

    # Simular apply_hybrid_05_postprocess: incrementa covered de "a"
    coverage_stats["a"]["covered"] += 1
    coverage_stats["a"]["unmet"] = max(0, coverage_stats["a"]["unmet"] - 1)
    # coverage_pct de "a" sigue siendo 0.0 (stale)

    # Simular apply_repair_if_beneficial: crea cs_copy y la promueve
    import copy as _copy
    cs_copy = {k: dict(v) for k, v in coverage_stats.items()}
    cs_copy["c"]["covered"] += 1                              # repair cubre slot de "c"
    cs_copy["c"]["unmet"] = max(0, cs_copy["c"]["unmet"] - 1)
    # coverage_pct de "c" sigue siendo 0.0 en cs_copy
    coverage_stats.clear()
    coverage_stats.update(cs_copy)

    # Estado inconsistente justo antes del fix:
    assert coverage_stats["a"]["covered"] == 1
    assert coverage_stats["a"]["coverage_pct"] == 0.0   # stale — el bug original
    assert coverage_stats["c"]["covered"] == 1
    assert coverage_stats["c"]["coverage_pct"] == 0.0   # stale — el bug original

    # Aplicar el fix
    recalculate_coverage_percentages(coverage_stats)

    # Construir coverage_details como lo hace generate_ai()
    details = _build_coverage_details(coverage_stats)

    # Criterio de corrección: ningún entry stale
    _assert_no_stale_pct(details)

    # Valores exactos
    assert details["a"]["coverage_pct"] == 25.0    # 1/4 * 100
    assert details["b"]["coverage_pct"] == 100.0   # sin cambios
    assert details["c"]["coverage_pct"] == 100.0   # 1/1 * 100
    assert details["a"]["unmet"] == 3
    assert details["c"]["unmet"] == 0


@skip_if_unavailable
def test_build_coverage_details_exact_bug_case():
    """
    Integración: reproduce el caso exacto reportado:
      demanded=4, covered=1, unmet=3, coverage_pct=0.0   → coverage_pct debe ser 25.0
      demanded=2, covered=1, unmet=1, coverage_pct=0.0   → coverage_pct debe ser 50.0
    """
    dm_a = _make_demand(need=4, wsname="ENLACE")
    dm_b = _make_demand(need=2, wsname="PARRILLERO")

    coverage_stats = {
        "a": _make_cs(dm_a, covered=1, unmet=3, coverage_pct=0.0),
        "b": _make_cs(dm_b, covered=1, unmet=1, coverage_pct=0.0),
    }

    recalculate_coverage_percentages(coverage_stats)
    details = _build_coverage_details(coverage_stats)

    _assert_no_stale_pct(details)
    assert details["a"]["demanded"] == 4
    assert details["a"]["covered"] == 1
    assert details["a"]["coverage_pct"] == 25.0
    assert details["b"]["demanded"] == 2
    assert details["b"]["covered"] == 1
    assert details["b"]["coverage_pct"] == 50.0


@skip_if_unavailable
def test_build_coverage_details_repair_engine_increments_only():
    """
    Integración: el RepairEngine solo modifica covered/unmet, nunca coverage_pct.
    Simula el patrón exact de _add_assignment() en repair_engine.py:
      cs["covered"] = cs.get("covered", 0) + 1
      cs["unmet"]   = max(0, cs.get("unmet", 0) - 1)
    El JSON resultante no debe tener pct stale.
    """
    dm = _make_demand(need=3, wsname="ENLACE")
    # Estado inicial: 1 cubierto, pct=33.3 (correcto en generar)
    coverage_stats = {
        "x": _make_cs(dm, covered=1, unmet=2, coverage_pct=33.3),
    }

    # RepairEngine añade un segundo slot sin actualizar coverage_pct
    cs = coverage_stats["x"]
    cs["covered"] = cs.get("covered", 0) + 1
    cs["unmet"] = max(0, cs.get("unmet", 0) - 1)
    # covered=2, unmet=1, coverage_pct=33.3 (stale; debería ser 66.7)

    recalculate_coverage_percentages(coverage_stats)
    details = _build_coverage_details(coverage_stats)

    _assert_no_stale_pct(details)
    assert details["x"]["coverage_pct"] == round(2 / 3 * 100, 1)  # 66.7
    assert details["x"]["unmet"] == 1


@skip_if_unavailable
def test_build_coverage_details_hybrid05_increments_only():
    """
    Integración: apply_hybrid_05_postprocess() modifica covered/unmet pero no coverage_pct.
    El patrón exacto de agenda.py línea 660-662:
      coverage_stats[dm.id]["covered"] += 1
      coverage_stats[dm.id]["met"]     += 1
      coverage_stats[dm.id]["unmet"]   = max(0, coverage_stats[dm.id]["unmet"] - 1)
    """
    dm = _make_demand(need=2, wsname="BARRA")
    coverage_stats = {
        "y": _make_cs(dm, covered=0, unmet=2, coverage_pct=0.0),
    }

    # Simular hybrid05 postprocess
    coverage_stats["y"]["covered"] += 1
    coverage_stats["y"]["met"] = coverage_stats["y"].get("met", 0) + 1
    coverage_stats["y"]["unmet"] = max(0, coverage_stats["y"]["unmet"] - 1)
    # covered=1, unmet=1, coverage_pct=0.0 (stale)

    recalculate_coverage_percentages(coverage_stats)
    details = _build_coverage_details(coverage_stats)

    _assert_no_stale_pct(details)
    assert details["y"]["coverage_pct"] == 50.0
    assert details["y"]["unmet"] == 1


@skip_if_unavailable
def test_no_stale_coverage_pct_invariant_holds_for_large_schedule():
    """
    Invariante global: tras recalculate, para todo entry en coverage_details:
      IF covered > 0 AND demanded > 0 THEN coverage_pct > 0.0
    Válido para schedules de tamaño realista (119 demandas).
    """
    import random

    random.seed(42)
    coverage_stats = {}
    for i in range(119):
        need = random.randint(1, 4)
        covered = random.randint(0, need)
        # Simular estado stale: coverage_pct siempre 0.0 (como salía el bug)
        dm = types.SimpleNamespace(
            id=f"dm-{i}",
            need=need,
            wsname=f"WS-{i % 5}",
            date=date(2026, 6, 20),
            start=time(10, 0),
            end=time(14, 0),
            wsid=f"ws-{i % 5}",
        )
        coverage_stats[f"dm-{i}"] = {
            "demand": dm,
            "met": covered,
            "covered": covered,
            "unmet": need - covered,
            "coverage_pct": 0.0,  # stale
            "employees": [],
        }

    recalculate_coverage_percentages(coverage_stats)
    details = _build_coverage_details(coverage_stats)

    _assert_no_stale_pct(details)

    # Verificar también la relación unmet = demanded - covered
    for k, v in details.items():
        assert v["unmet"] == max(v["demanded"] - v["covered"], 0), (
            f"Entry {k}: unmet={v['unmet']} != demanded-covered={v['demanded']-v['covered']}"
        )
