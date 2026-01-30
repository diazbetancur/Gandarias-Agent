# services/explicador_huecos.py
from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, date, time, timedelta
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple
import json
from uuid import uuid4


# =========================
# 1) CATEGORÍAS (HU 1.1)
# =========================
class CategoriaHueco(str, Enum):
    FALTA_DE_PERSONAL = "FALTA_DE_PERSONAL"
    RESTRICCIONES_LEGALES = "RESTRICCIONES_LEGALES"
    INCOMPATIBILIDAD_DE_TURNOS = "INCOMPATIBILIDAD_DE_TURNOS"
    DESCANSOS_OBLIGATORIOS = "DESCANSOS_OBLIGATORIOS"
    HORAS_MAXIMAS_CONTRATADAS = "HORAS_MAXIMAS_CONTRATADAS"
    CONTRADICCION_DE_REGLAS = "CONTRADICCION_DE_REGLAS"
    LIMITACIONES_OPERATIVAS = "LIMITACIONES_OPERATIVAS"


# =========================
# 2) CÓDIGOS DE RAZÓN
# =========================
class CodigoRazon(str, Enum):
    SKILL_FALTANTE = "SKILL_FALTANTE"
    FUERA_DE_VENTANA = "FUERA_DE_VENTANA"
    SOLAPE_TURNO = "SOLAPE_TURNO"
    DESCANSO_LEGAL_MINIMO = "DESCANSO_LEGAL_MINIMO"
    MAX_HORAS_SEMANALES = "MAX_HORAS_SEMANALES"
    MAX_DIAS_CONSECUTIVOS = "MAX_DIAS_CONSECUTIVOS"
    REGLA_NEGOCIO_BLOQUEA = "REGLA_NEGOCIO_BLOQUEA"
    LIMITE_OPERATIVO = "LIMITE_OPERATIVO"
    SIN_CANDIDATOS = "SIN_CANDIDATOS"


# =========================
# 3) MODELO DE HUECO DETECTADO
# =========================
@dataclass(frozen=True)
class HuecoNoCubierto:
    inicio: datetime
    fin: datetime
    workstation_id: Optional[Any]
    workstation_nombre: str
    requerido: float
    asignado: float
    faltante: float
    agenda_id: Optional[Any] = None

    @property
    def fecha_hueco(self) -> date:
        return self.inicio.date()

    @property
    def duracion_minutos(self) -> int:
        return int((self.fin - self.inicio).total_seconds() // 60)


# =========================
# 4) CONTEXTO (ADAPTADO A prueba_2.py)
# =========================
@dataclass
class ContextoExplicacion:
    empleados: List[Any]
    asignaciones_por_empleado: Dict[Any, List[Tuple[datetime, datetime, Any]]]

    def empleado_id(self, e: Any) -> Any:
        return getattr(e, "id")

    def empleado_nombre(self, e: Any) -> str:
        return getattr(e, "name", getattr(e, "nombre", str(self.empleado_id(e))))

    def tiene_skill(self, e: Any, workstation_id: Any) -> bool:
        fn = getattr(e, "can", None)
        if callable(fn) and workstation_id is not None:
            return bool(fn(workstation_id))
        return True

    def esta_disponible(self, e: Any, inicio: datetime, fin: datetime) -> bool:
        fn = getattr(e, "available", None)
        if callable(fn):
            day = inicio.date()
            st = inicio.time()
            en = fin.time()
            return bool(fn(day, st, en))
        return True

    def hay_solape(self, empleado_id: Any, inicio: datetime, fin: datetime) -> bool:
        for (a_ini, a_fin, _ws) in self.asignaciones_por_empleado.get(empleado_id, []):
            if not (fin <= a_ini or inicio >= a_fin):
                return True
        return False

    def viola_descanso_legal_minimo(self, e: Any, inicio: datetime) -> bool:
        # Stub (engancha LawRestrictions si lo tienes en Emp)
        min_rest = getattr(e, "min_rest_hours", None)
        if min_rest is None:
            return False

        empleado_id = self.empleado_id(e)
        asigns = self.asignaciones_por_empleado.get(empleado_id, [])
        if not asigns:
            return False

        prev_end = max((a_fin for (a_ini, a_fin, _ws) in asigns if a_fin <= inicio), default=None)
        if prev_end is None:
            return False

        horas = (inicio - prev_end).total_seconds() / 3600
        return horas < float(min_rest)

    def viola_max_horas(self, e: Any, inicio: datetime, fin: datetime) -> bool:
        max_week = getattr(e, "max_week_hours", None)
        if max_week is None:
            return False

        empleado_id = self.empleado_id(e)
        total_horas = 0.0
        for (a_ini, a_fin, _ws) in self.asignaciones_por_empleado.get(empleado_id, []):
            total_horas += (a_fin - a_ini).total_seconds() / 3600

        nuevo = (fin - inicio).total_seconds() / 3600
        return (total_horas + nuevo) > float(max_week)

    def otras_reglas_bloquean(self, e: Any, hueco: HuecoNoCubierto) -> Optional[str]:
        return None


# =========================
# Helpers
# =========================
def build_asignaciones_por_empleado(
    week: List[date],
    sched: Dict[date, List[Tuple[Any, Any]]],
) -> Dict[Any, List[Tuple[datetime, datetime, Any]]]:
    """
    Convierte sched[date] = [(emp, dm), ...] a:
      emp_id -> [(dt_inicio, dt_fin, wsid)]
    Ignora ausencias (wsid None).
    """
    out: Dict[Any, List[Tuple[datetime, datetime, Any]]] = {}

    for d in week:
        for emp, dm in (sched.get(d) or []):
            wsid = getattr(dm, "wsid", None)
            if wsid is None:
                continue
            st = getattr(dm, "start", None)
            en = getattr(dm, "end", None)
            if st is None or en is None:
                continue

            ini = datetime.combine(d, st)
            fin = datetime.combine(d, en)
            if en == time(0, 0) or fin <= ini:
                fin = datetime.combine(d + timedelta(days=1), en)

            out.setdefault(emp.id, []).append((ini, fin, wsid))

    return out


# =========================
# 5) SERVICIO PRINCIPAL
# =========================
class ExplicadorHuecosService:
    def __init__(
        self,
        cursor,
        table_name: str = '"Management"."ScheduleGaps"',
        debug: bool = True,
    ):
        self.cur = cursor
        self.table_name = table_name
        self.debug = debug
        self._wsid_cache: Dict[str, Optional[str]] = {}

    def _log(self, msg: str) -> None:
        if self.debug:
            print(msg)

    def _resolve_wsid_by_name(self, wsname: str) -> Optional[str]:
        """
        Busca WorkstationId por nombre en Management.Workstations.
        Cachea resultados para no spamear DB.
        """
        if not wsname:
            return None

        if wsname in self._wsid_cache:
            return self._wsid_cache[wsname]

        # 1) exact match
        self.cur.execute(
            'SELECT "Id" FROM "Management"."Workstations" WHERE "Name" = %s LIMIT 1',
            (wsname,),
        )
        row = self.cur.fetchone()
        if row and row[0]:
            self._wsid_cache[wsname] = str(row[0])
            return self._wsid_cache[wsname]

        # 2) fallback ilike
        self.cur.execute(
            'SELECT "Id","Name" FROM "Management"."Workstations" WHERE "Name" ILIKE %s LIMIT 1',
            (wsname,),
        )
        row = self.cur.fetchone()
        if row and row[0]:
            self._wsid_cache[wsname] = str(row[0])
            self._log(f'[HU1.1][WSID] ILIKE match: "{wsname}" -> "{row[1]}" ({row[0]})')
            return self._wsid_cache[wsname]

        self._wsid_cache[wsname] = None
        self._log(f'[HU1.1][WSID][WARN] No pude resolver WorkstationId para "{wsname}"')
        return None

    # ---------- detectar huecos ----------
    def detectar_huecos(self, agenda_result: Any) -> List[HuecoNoCubierto]:
        huecos: List[HuecoNoCubierto] = []

        if not isinstance(agenda_result, dict):
            self._log("[HU1.1][DETECT][WARN] agenda_result no es dict; no puedo detectar huecos.")
            return huecos

        keys = list(agenda_result.keys())
        self._log(f"[HU1.1][DETECT] res keys={keys}")

        # A) Si algún día agregas unmet_segments, lo soportamos
        unmet_segments = agenda_result.get("unmet_segments") or []
        unmet_demands = agenda_result.get("unmet_demands") or []
        if unmet_segments:
            self._log(f"[HU1.1][DETECT] usando unmet_segments: {len(unmet_segments)} segmentos.")
            by_demand_id = {d.get("demand_id"): d for d in unmet_demands if d.get("demand_id") is not None}

            for seg in unmet_segments:
                faltante = float(seg.get("unmet", 0.0) or 0.0)
                if faltante <= 0:
                    continue

                demand_id = seg.get("demand_id")
                d = by_demand_id.get(demand_id, {}) if demand_id is not None else {}

                requerido = float(d.get("required", faltante))
                covered = float(d.get("covered", max(0.0, requerido - faltante)))
                asignado = covered

                wsid = seg.get("wsid") or d.get("wsid")
                wsname = seg.get("wsname") or d.get("wsname") or str(wsid)

                day = datetime.strptime(seg["date"], "%Y-%m-%d").date()
                st = datetime.strptime(seg["start"], "%H:%M").time()
                en = datetime.strptime(seg["end"], "%H:%M").time()

                inicio = datetime.combine(day, st)
                fin = datetime.combine(day, en)
                if en == time(0, 0) or fin <= inicio:
                    fin = datetime.combine(day + timedelta(days=1), en)

                huecos.append(
                    HuecoNoCubierto(
                        inicio=inicio,
                        fin=fin,
                        workstation_id=wsid,
                        workstation_nombre=wsname,
                        requerido=requerido,
                        asignado=asignado,
                        faltante=faltante,
                        agenda_id=agenda_result.get("schedule_id") or agenda_result.get("id"),
                    )
                )

            self._log(f"[HU1.1][DETECT] huecos detectados={len(huecos)} (desde unmet_segments).")
            return huecos

        # B) HU1.1 real en tu proyecto: usar coverage_details (SÍ existe en generate_flexible)
        coverage_details = agenda_result.get("coverage_details") or {}
        if not coverage_details:
            self._log("[HU1.1][DETECT] res no tiene coverage_details; huecos=0.")
            return huecos

        self._log(f"[HU1.1][DETECT] usando coverage_details: {len(coverage_details)} demandas.")

        for demand_id, cd in coverage_details.items():
            try:
                unmet = float(cd.get("unmet", 0.0) or 0.0)
            except Exception:
                unmet = 0.0
            if unmet <= 0:
                continue

            wsname = cd.get("workstation") or "UNKNOWN"
            date_str = cd.get("date")
            time_str = cd.get("time")  # "HH:MM-HH:MM"
            if not date_str or not time_str or "-" not in time_str:
                self._log(f"[HU1.1][DETECT][WARN] demand_id={demand_id} sin date/time válido: {cd}")
                continue

            st_s, en_s = time_str.split("-", 1)
            day = datetime.strptime(date_str, "%Y-%m-%d").date()
            st = datetime.strptime(st_s.strip(), "%H:%M").time()
            en = datetime.strptime(en_s.strip(), "%H:%M").time()

            inicio = datetime.combine(day, st)
            fin = datetime.combine(day, en)
            if en == time(0, 0) or fin <= inicio:
                fin = datetime.combine(day + timedelta(days=1), en)

            requerido = float(cd.get("demanded", unmet) or unmet)
            asignado = float(cd.get("covered", 0.0) or 0.0)
            faltante = unmet

            wsid = cd.get("workstation_id") or cd.get("wsid")
            if not wsid:
                wsid = self._resolve_wsid_by_name(wsname)

            huecos.append(
                HuecoNoCubierto(
                    inicio=inicio,
                    fin=fin,
                    workstation_id=str(wsid) if wsid else None,
                    workstation_nombre=wsname,
                    requerido=requerido,
                    asignado=asignado,
                    faltante=faltante,
                    agenda_id=agenda_result.get("schedule_id") or agenda_result.get("id"),
                )
            )

        self._log(f"[HU1.1][DETECT] huecos detectados={len(huecos)} (desde coverage_details).")
        if huecos[:3]:
            self._log("[HU1.1][DETECT] ejemplo huecos (primeros 3):")
            for h in huecos[:3]:
                self._log(
                    f"  - {h.workstation_nombre} {h.inicio:%Y-%m-%d %H:%M}-{h.fin:%H:%M} faltante={h.faltante}"
                )
        return huecos

    # ---------- explicar hueco ----------
    def explicar_hueco(self, hueco: HuecoNoCubierto, ctx: ContextoExplicacion) -> Dict[str, Any]:
        total_empleados = len(ctx.empleados)
        breakdown: Dict[CodigoRazon, int] = {k: 0 for k in CodigoRazon}
        ejemplos: Dict[str, List[str]] = {k.value: [] for k in CodigoRazon}
        max_ejemplos = 5

        for e in ctx.empleados:
            eid = ctx.empleado_id(e)
            nombre = ctx.empleado_nombre(e)

            if not ctx.tiene_skill(e, hueco.workstation_id):
                breakdown[CodigoRazon.SKILL_FALTANTE] += 1
                if len(ejemplos[CodigoRazon.SKILL_FALTANTE.value]) < max_ejemplos:
                    ejemplos[CodigoRazon.SKILL_FALTANTE.value].append(nombre)
                continue

            if not ctx.esta_disponible(e, hueco.inicio, hueco.fin):
                breakdown[CodigoRazon.FUERA_DE_VENTANA] += 1
                if len(ejemplos[CodigoRazon.FUERA_DE_VENTANA.value]) < max_ejemplos:
                    ejemplos[CodigoRazon.FUERA_DE_VENTANA.value].append(nombre)
                continue

            if ctx.hay_solape(eid, hueco.inicio, hueco.fin):
                breakdown[CodigoRazon.SOLAPE_TURNO] += 1
                if len(ejemplos[CodigoRazon.SOLAPE_TURNO.value]) < max_ejemplos:
                    ejemplos[CodigoRazon.SOLAPE_TURNO.value].append(nombre)
                continue

            if ctx.viola_descanso_legal_minimo(e, hueco.inicio):
                breakdown[CodigoRazon.DESCANSO_LEGAL_MINIMO] += 1
                if len(ejemplos[CodigoRazon.DESCANSO_LEGAL_MINIMO.value]) < max_ejemplos:
                    ejemplos[CodigoRazon.DESCANSO_LEGAL_MINIMO.value].append(nombre)
                continue

            if ctx.viola_max_horas(e, hueco.inicio, hueco.fin):
                breakdown[CodigoRazon.MAX_HORAS_SEMANALES] += 1
                if len(ejemplos[CodigoRazon.MAX_HORAS_SEMANALES.value]) < max_ejemplos:
                    ejemplos[CodigoRazon.MAX_HORAS_SEMANALES.value].append(nombre)
                continue

            regla = ctx.otras_reglas_bloquean(e, hueco)
            if regla:
                breakdown[CodigoRazon.REGLA_NEGOCIO_BLOQUEA] += 1
                if len(ejemplos[CodigoRazon.REGLA_NEGOCIO_BLOQUEA.value]) < max_ejemplos:
                    ejemplos[CodigoRazon.REGLA_NEGOCIO_BLOQUEA.value].append(f"{nombre} ({regla})")
                continue

            breakdown[CodigoRazon.LIMITE_OPERATIVO] += 1
            if len(ejemplos[CodigoRazon.LIMITE_OPERATIVO.value]) < max_ejemplos:
                ejemplos[CodigoRazon.LIMITE_OPERATIVO.value].append(nombre)

        if total_empleados == 0:
            breakdown[CodigoRazon.SIN_CANDIDATOS] += 1

        categoria = self._clasificar_categoria(breakdown)
        acciones = self._acciones_sugeridas(categoria, hueco, breakdown)
        resumen = self._armar_resumen(categoria, hueco, breakdown)

        return {
            "agenda_id": hueco.agenda_id,
            "workstation": {"id": hueco.workstation_id, "nombre": hueco.workstation_nombre},
            "slot": {"inicio": hueco.inicio.isoformat(), "fin": hueco.fin.isoformat()},
            "cobertura": {"requerido": hueco.requerido, "asignado": hueco.asignado, "faltante": hueco.faltante},
            "categoria": categoria.value,
            "resumen": resumen,
            "razones": {k.value: breakdown[k] for k in breakdown if breakdown[k] > 0},
            "ejemplos": {k: v for k, v in ejemplos.items() if v},
            "acciones_sugeridas": acciones,
        }

    def _clasificar_categoria(self, breakdown: Dict[CodigoRazon, int]) -> CategoriaHueco:
        orden = sorted(breakdown.items(), key=lambda kv: kv[1], reverse=True)
        top, top_n = orden[0][0], orden[0][1]
        if top_n == 0:
            return CategoriaHueco.LIMITACIONES_OPERATIVAS
        if top in (CodigoRazon.SKILL_FALTANTE, CodigoRazon.SIN_CANDIDATOS, CodigoRazon.FUERA_DE_VENTANA):
            return CategoriaHueco.FALTA_DE_PERSONAL
        if top in (CodigoRazon.DESCANSO_LEGAL_MINIMO,):
            return CategoriaHueco.DESCANSOS_OBLIGATORIOS
        if top in (CodigoRazon.MAX_HORAS_SEMANALES,):
            return CategoriaHueco.HORAS_MAXIMAS_CONTRATADAS
        if top in (CodigoRazon.SOLAPE_TURNO,):
            return CategoriaHueco.INCOMPATIBILIDAD_DE_TURNOS
        if top in (CodigoRazon.REGLA_NEGOCIO_BLOQUEA,):
            return CategoriaHueco.CONTRADICCION_DE_REGLAS
        return CategoriaHueco.LIMITACIONES_OPERATIVAS

    def _armar_resumen(self, categoria: CategoriaHueco, hueco: HuecoNoCubierto, breakdown: Dict[CodigoRazon, int]) -> str:
        partes = []
        if breakdown.get(CodigoRazon.SKILL_FALTANTE, 0) > 0:
            partes.append(f"{breakdown[CodigoRazon.SKILL_FALTANTE]} sin skill")
        if breakdown.get(CodigoRazon.FUERA_DE_VENTANA, 0) > 0:
            partes.append(f"{breakdown[CodigoRazon.FUERA_DE_VENTANA]} fuera de ventana")
        if breakdown.get(CodigoRazon.SOLAPE_TURNO, 0) > 0:
            partes.append(f"{breakdown[CodigoRazon.SOLAPE_TURNO]} con solape")
        if breakdown.get(CodigoRazon.DESCANSO_LEGAL_MINIMO, 0) > 0:
            partes.append(f"{breakdown[CodigoRazon.DESCANSO_LEGAL_MINIMO]} por descanso legal")
        if breakdown.get(CodigoRazon.MAX_HORAS_SEMANALES, 0) > 0:
            partes.append(f"{breakdown[CodigoRazon.MAX_HORAS_SEMANALES]} por tope de horas")
        if breakdown.get(CodigoRazon.REGLA_NEGOCIO_BLOQUEA, 0) > 0:
            partes.append(f"{breakdown[CodigoRazon.REGLA_NEGOCIO_BLOQUEA]} por regla de negocio")

        detalle = "; ".join(partes) if partes else "sin candidatos elegibles"
        return (
            f"Hueco no cubierto en {hueco.workstation_nombre} "
            f"({hueco.inicio:%Y-%m-%d %H:%M} a {hueco.fin:%H:%M}). "
            f"Faltan {hueco.faltante:.2f} cupos. "
            f"Categoría: {categoria.value}. Causas principales: {detalle}."
        )

    def _acciones_sugeridas(self, categoria: CategoriaHueco, hueco: HuecoNoCubierto, breakdown: Dict[CodigoRazon, int]) -> List[str]:
        ws = hueco.workstation_nombre
        acciones: List[str] = []

        if categoria == CategoriaHueco.FALTA_DE_PERSONAL:
            if breakdown.get(CodigoRazon.SKILL_FALTANTE, 0) > 0:
                acciones.append(f"Capacitar/autorizar más personal para cubrir {ws} (skill).")
            if breakdown.get(CodigoRazon.FUERA_DE_VENTANA, 0) > 0:
                acciones.append("Ajustar ventanas UserShift/disponibilidad para ese horario o contratar refuerzo.")
            acciones.append("Revisar si la demanda (requerido) está sobreestimada para ese slot.")
            return acciones

        if categoria in (CategoriaHueco.DESCANSOS_OBLIGATORIOS, CategoriaHueco.RESTRICCIONES_LEGALES):
            acciones.append("Revisar restricción de descanso mínimo entre turnos (LawRestrictions).")
            acciones.append("Re-balancear turnos para respetar descansos.")
            return acciones

        if categoria == CategoriaHueco.HORAS_MAXIMAS_CONTRATADAS:
            acciones.append("Aumentar horas contratadas o habilitar horas extra (si aplica).")
            acciones.append("Redistribuir carga semanal a personal con horas disponibles.")
            return acciones

        if categoria == CategoriaHueco.INCOMPATIBILIDAD_DE_TURNOS:
            acciones.append("Revisar solapes de turnos; ajustar asignaciones previas.")
            acciones.append("Permitir swap/rotación para liberar el slot del hueco.")
            return acciones

        if categoria == CategoriaHueco.CONTRADICCION_DE_REGLAS:
            acciones.append("Identificar la regla que bloquea (pairing hyb 0.5, fairness hard, etc.).")
            acciones.append("Relajar esa regla o moverla a soft-constraint con penalización.")
            return acciones

        acciones.append("Revisar límites operativos (capacidad por estación, máximos simultáneos, etc.).")
        return acciones

    # ---------- persistir en ScheduleGaps ----------
    def guardar_schedule_gaps(
        self,
        explicaciones: List[Dict[str, Any]],
        token: str,
    ) -> int:
        if not explicaciones:
            self._log("[HU1.1][DB] 0 explicaciones -> no inserto nada.")
            return 0

        sql = f"""
            INSERT INTO {self.table_name}
              ("Id","Date","WorkstationId","StartTime","EndTime","GapExplanation","GapCategory","Token","CreatedAt")
            VALUES
              (%s,%s,%s,%s,%s,%s,%s,%s,%s)
        """

        inserted = 0
        now_dt = datetime.utcnow()

        for exp in explicaciones:
            wsid = exp["workstation"].get("id")
            wsname = exp["workstation"].get("nombre")

            # Si no tengo wsid, intento resolver (otra vez) por nombre
            if not wsid and wsname:
                wsid = self._resolve_wsid_by_name(wsname)

            if not wsid:
                self._log(f'[HU1.1][DB][SKIP] Sin WorkstationId (ws="{wsname}") -> no inserto.')
                continue

            ini = datetime.fromisoformat(exp["slot"]["inicio"])
            fin = datetime.fromisoformat(exp["slot"]["fin"])

            # Usamos interval (timedelta) igual que Schedules
            st_td = timedelta(hours=ini.hour, minutes=ini.minute)
            en_td = timedelta(hours=fin.hour, minutes=fin.minute)

            payload = json.dumps(exp, ensure_ascii=False)

            self.cur.execute(
                sql,
                (
                    str(uuid4()),
                    ini.date(),
                    str(wsid),
                    st_td,
                    en_td,
                    payload,
                    exp.get("categoria"),
                    token,
                    now_dt,
                ),
            )
            inserted += 1

        self._log(f"[HU1.1][DB] inserted={inserted} rows into {self.table_name} token={token}")
        return inserted

    # ---------- Orquestación ----------
    def generar_y_guardar(
        self,
        agenda_result: Any,
        ctx: ContextoExplicacion,
        token: str,
    ) -> List[Dict[str, Any]]:
        self._log(f"[HU1.1] ==== START generar_y_guardar token={token} ====")
        total_unmet = (agenda_result.get("summary") or {}).get("total_unmet") if isinstance(agenda_result, dict) else None
        self._log(f"[HU1.1] summary.total_unmet={total_unmet}")

        huecos = self.detectar_huecos(agenda_result)
        self._log(f"[HU1.1] huecos_detectados={len(huecos)}")

        explicaciones = [self.explicar_hueco(h, ctx) for h in huecos]
        self._log(f"[HU1.1] explicaciones_generadas={len(explicaciones)}")

        inserted = self.guardar_schedule_gaps(explicaciones, token=token)
        self._log(f"[HU1.1] ==== END generar_y_guardar inserted={inserted} ====")
        return explicaciones
