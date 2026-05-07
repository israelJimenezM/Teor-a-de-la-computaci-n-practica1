"""
Teoría de la Computación - ESCOM IPN
Aplicación interactiva para:
  - Prefijos, Sufijos, Subcadenas, Cerraduras (Prácticas anteriores)
  - Simulación de AFD, AFND, AFN-λ (Práctica 3)
  - Minimización de AFD (Práctica 3)
  - Conversión AFD → ER por eliminación de estados (Práctica 4)
  - Validadores con Expresiones Regulares (Práctica 4)
  - Importación de archivos .jff de JFLAP
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import math
import re
import xml.etree.ElementTree as ET
import json
import os
from collections import defaultdict, deque
import itertools

# ─────────────────────────────────────────────
#  COLORES  (estética tipo JFLAP modernizado)
# ─────────────────────────────────────────────
BG        = "#1e1e2e"
BG2       = "#2a2a3e"
BG3       = "#313150"
ACCENT    = "#7c6af7"
ACCENT2   = "#a78bfa"
FG        = "#e2e8f0"
FG2       = "#94a3b8"
STATE_COL = "#4f46e5"
STATE_ACC = "#059669"
STATE_INI = "#d97706"
EDGE_COL  = "#7c6af7"
ACTIVE    = "#f59e0b"
BTN_BG    = "#4f46e5"
BTN_FG    = "#ffffff"
ENTRY_BG  = "#252540"
RED       = "#ef4444"
GREEN     = "#22c55e"

# ─────────────────────────────────────────────
#  UTILIDADES – Cadenas
# ─────────────────────────────────────────────

def prefijos(cadena, vacia):
    res = (["λ"] if vacia else [])
    for i in range(1, len(cadena)+1):
        res.append(cadena[:i])
    return res

def sufijos(cadena, vacia):
    res = (["λ"] if vacia else [])
    for i in range(1, len(cadena)+1):
        res.append(cadena[len(cadena)-i:])
    return res

def subcadenas(cadena, vacia):
    res = (["λ"] if vacia else [])
    seen = set()
    for i in range(len(cadena)):
        for j in range(i+1, len(cadena)+1):
            s = cadena[i:j]
            if s not in seen:
                seen.add(s)
                res.append(s)
    return res

def parse_alfabeto(texto):
    texto = texto.strip()
    if "," in texto:
        return [p.strip() for p in texto.split(",") if p.strip()]
    if " " in texto:
        return texto.split()
    return list(texto)

def generar_kleene(alfabeto, n, incluir_vacia):
    res = ["λ"] if incluir_vacia else []
    cola = deque(alfabeto)
    while cola:
        actual = cola.popleft()
        if len(actual) <= n:
            res.append(actual)
        if len(actual) < n:
            for s in alfabeto:
                cola.append(actual + s)
    return res

# ─────────────────────────────────────────────
#  CLASE AUTÓMATA
# ─────────────────────────────────────────────

class Automata:
    """Representa AFD, AFND o AFN-λ"""

    def __init__(self):
        self.reset()

    def reset(self):
        self.states      = []          # lista de nombres
        self.alphabet    = []          # lista de símbolos (sin λ)
        self.transitions = defaultdict(lambda: defaultdict(set))  # t[estado][símbolo] = {estados}
        self.initial     = None
        self.accepting   = set()
        self.tipo        = "AFD"       # "AFD", "AFND", "AFN-λ"

    # ── Operaciones básicas ──

    def add_state(self, name, initial=False, accepting=False):
        if name not in self.states:
            self.states.append(name)
        if initial:
            self.initial = name
        if accepting:
            self.accepting.add(name)

    def add_transition(self, src, sym, dst):
        self.transitions[src][sym].add(dst)
        if sym not in self.alphabet and sym != "λ":
            self.alphabet.append(sym)

    def remove_state(self, name):
        if name in self.states:
            self.states.remove(name)
        if self.initial == name:
            self.initial = None
        self.accepting.discard(name)
        if name in self.transitions:
            del self.transitions[name]
        for s in self.transitions:
            for sym in list(self.transitions[s]):
                self.transitions[s][sym].discard(name)

    # ── Simulación AFD ──

    def simular_afd(self, cadena):
        """Devuelve (aceptada, traza)"""
        if self.initial is None:
            return False, []
        estado = self.initial
        traza  = [(estado, None)]
        for sym in cadena:
            dsts = self.transitions[estado].get(sym, set())
            if len(dsts) != 1:
                return False, traza
            estado = next(iter(dsts))
            traza.append((estado, sym))
        return estado in self.accepting, traza

    # ── Lambda clausura ──

    def lambda_clausura(self, estados):
        clausura = set(estados)
        pila     = list(estados)
        while pila:
            q = pila.pop()
            for r in self.transitions[q].get("λ", set()):
                if r not in clausura:
                    clausura.add(r)
                    pila.append(r)
        return frozenset(clausura)

    def lambda_clausura_single(self, estado):
        return self.lambda_clausura({estado})

    # ── Simulación AFND / AFN-λ ──

    def simular_nd(self, cadena):
        """Devuelve (aceptada, pasos). pasos = lista de conjuntos de estados."""
        if self.initial is None:
            return False, []
        actuales = self.lambda_clausura({self.initial})
        pasos    = [set(actuales)]
        for sym in cadena:
            siguientes = set()
            for q in actuales:
                for r in self.transitions[q].get(sym, set()):
                    siguientes.add(r)
            actuales = self.lambda_clausura(siguientes)
            pasos.append(set(actuales))
        aceptada = bool(actuales & self.accepting)
        return aceptada, pasos

    # ── Conversión AFND → AFD (subconjuntos) ──

    def a_afd(self):
        """Retorna un nuevo Automata AFD equivalente."""
        if self.initial is None:
            return Automata()
        afd = Automata()
        afd.tipo = "AFD"
        inicio   = self.lambda_clausura({self.initial})
        cola     = deque([inicio])
        vistos   = {inicio: self._nombre_conjunto(inicio)}

        afd.add_state(vistos[inicio],
                      initial=True,
                      accepting=bool(inicio & self.accepting))

        while cola:
            conj = cola.popleft()
            nombre_src = vistos[conj]
            for sym in self.alphabet:
                siguientes = set()
                for q in conj:
                    for r in self.transitions[q].get(sym, set()):
                        siguientes.add(r)
                dest = self.lambda_clausura(siguientes)
                if not dest:
                    continue
                if dest not in vistos:
                    vistos[dest] = self._nombre_conjunto(dest)
                    cola.append(dest)
                    afd.add_state(vistos[dest],
                                  accepting=bool(dest & self.accepting))
                afd.add_transition(nombre_src, sym, vistos[dest])
        afd.alphabet = list(self.alphabet)
        return afd

    def _nombre_conjunto(self, conj):
        return "{" + ",".join(sorted(conj)) + "}"

    # ── Minimización AFD (Hopcroft) ──

    def minimizar(self):
        """Retorna (afd_min, grupos) donde grupos es lista de frozensets."""
        # Eliminar estados inaccesibles
        accesibles = self._estados_accesibles()
        estados  = [s for s in self.states if s in accesibles]
        aceptan  = self.accepting & set(estados)
        no_acept = set(estados) - aceptan

        if not aceptan:
            # Sin estados de aceptación, todos equivalentes
            grupos = [frozenset(no_acept)]
        else:
            grupos = [frozenset(aceptan), frozenset(no_acept)]
        grupos = [g for g in grupos if g]

        # Refinamiento
        cambiado = True
        while cambiado:
            cambiado    = False
            nuevos_grp  = []
            for grupo in grupos:
                splits = self._split(grupo, grupos)
                if len(splits) > 1:
                    cambiado = True
                nuevos_grp.extend(splits)
            grupos = nuevos_grp

        # Construir AFD mínimo
        min_afd = Automata()
        min_afd.tipo = "AFD"
        rep = {}   # estado → nombre del grupo
        nombres_grp = {}
        for i, g in enumerate(grupos):
            nombre = "q" + str(i)
            nombres_grp[id(g)] = nombre
            for s in g:
                rep[s] = nombre

        for g in grupos:
            nombre = rep[next(iter(g))]
            es_ini = self.initial in g
            es_acc = bool(g & self.accepting)
            min_afd.add_state(nombre, initial=es_ini, accepting=es_acc)

        for g in grupos:
            src_rep = rep[next(iter(g))]
            rep_q   = next(iter(g))
            for sym in self.alphabet:
                dsts = self.transitions[rep_q].get(sym, set())
                for d in dsts:
                    if d in rep:
                        min_afd.add_transition(src_rep, sym, rep[d])
                        break
        min_afd.alphabet = list(self.alphabet)
        return min_afd, grupos

    def _estados_accesibles(self):
        if self.initial is None:
            return set()
        vistos = {self.initial}
        cola   = deque([self.initial])
        while cola:
            q = cola.popleft()
            for sym in self.transitions[q]:
                for r in self.transitions[q][sym]:
                    if r not in vistos:
                        vistos.add(r)
                        cola.append(r)
        return vistos

    def _split(self, grupo, particion):
        """Divide el grupo si hay estados distinguibles."""
        lista = list(grupo)
        if len(lista) == 1:
            return [grupo]
        grupo_de = {}
        for g in particion:
            for s in g:
                grupo_de[s] = g

        subgrupos = {}
        for estado in lista:
            key = []
            for sym in sorted(self.alphabet):
                dsts = self.transitions[estado].get(sym, set())
                if dsts:
                    dst = next(iter(dsts))
                    key.append((sym, id(grupo_de.get(dst, frozenset()))))
                else:
                    key.append((sym, None))
            key = tuple(key)
            subgrupos.setdefault(key, []).append(estado)

        return [frozenset(v) for v in subgrupos.values()]

    # ── Conversión AFD → ER (eliminación de estados) ──

    def afd_a_er(self):
        """
        Aplica el método de eliminación de estados (GNFA).
        Retorna (er_final, pasos) donde pasos es lista de descripciones.
        """
        # Construir GNFA con estado inicial nuevo qi y final nuevo qf
        estados  = list(self.states)
        qi, qf   = "__qi__", "__qf__"
        # r[src][dst] = expresión regular (None = vacío / ∅)
        r = defaultdict(lambda: defaultdict(lambda: None))

        # Transiciones originales
        for src in self.transitions:
            for sym in self.transitions[src]:
                for dst in self.transitions[src][sym]:
                    r[src][dst] = _er_union(r[src][dst], sym)

        # Transiciones del nuevo estado inicial
        r[qi][self.initial] = "λ"

        # Transiciones al nuevo estado final
        for acc in self.accepting:
            r[acc][qf] = _er_union(r[acc][qf], "λ")

        orden = [qi] + estados + [qf]
        pasos = []

        # Eliminar estados intermedios
        for elim in estados:
            desc  = f"Eliminando estado '{elim}'"
            self_loop = r[elim][elim]
            star  = f"({self_loop})*" if self_loop else "λ"

            for qi2 in orden:
                if qi2 == elim:
                    continue
                for qf2 in orden:
                    if qf2 == elim:
                        continue
                    r1 = r[qi2][elim]
                    r2 = r[elim][qf2]
                    if r1 is None or r2 is None:
                        continue
                    parte  = _er_concat(r1, _er_concat(star, r2)) if self_loop else _er_concat(r1, r2)
                    r[qi2][qf2] = _er_union(r[qi2][qf2], parte)

            # Borrar fila/col del estado eliminado
            for q in orden:
                r[q][elim] = None
                r[elim][q] = None

            er_actual = r[qi][qf] or "∅"
            pasos.append((desc, er_actual))

        return r[qi][qf] or "∅", pasos

    # ── Importar desde .jff (JFLAP) ──

    @staticmethod
    def desde_jff(path):
        """Lee un archivo .jff y retorna un Automata."""
        tree  = ET.parse(path)
        root  = tree.getroot()
        auto  = Automata()
        mtype = root.find("type")
        if mtype is not None:
            t = mtype.text.strip().lower()
            if "dfa" in t:
                auto.tipo = "AFD"
            elif "nfa" in t:
                auto.tipo = "AFND"
            else:
                auto.tipo = "AFD"

        maquina = root.find("automaton")
        if maquina is None:
            raise ValueError("No se encontró elemento <automaton> en el .jff")

        id_nombre = {}
        for state in maquina.findall("state"):
            sid  = state.get("id")
            name = state.get("name") or f"q{sid}"
            id_nombre[sid] = name
            ini  = state.find("initial") is not None
            acc  = state.find("final") is not None
            auto.add_state(name, initial=ini, accepting=acc)

        for trans in maquina.findall("transition"):
            src = id_nombre.get(trans.find("from").text, "?")
            dst = id_nombre.get(trans.find("to").text, "?")
            rlabel = trans.find("read")
            sym = rlabel.text if rlabel is not None and rlabel.text else "λ"
            auto.add_transition(src, sym, dst)

        return auto

    def guardar_json(self, path):
        data = {
            "tipo":       self.tipo,
            "states":     self.states,
            "alphabet":   self.alphabet,
            "initial":    self.initial,
            "accepting":  list(self.accepting),
            "transitions": {
                s: {sym: list(dsts) for sym, dsts in self.transitions[s].items()}
                for s in self.transitions
            }
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    @staticmethod
    def desde_json(path):
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        auto = Automata()
        auto.tipo     = data.get("tipo", "AFD")
        auto.states   = data["states"]
        auto.alphabet = data["alphabet"]
        auto.initial  = data["initial"]
        auto.accepting = set(data["accepting"])
        for s, syms in data["transitions"].items():
            for sym, dsts in syms.items():
                for d in dsts:
                    auto.transitions[s][sym].add(d)
        return auto


# ─────────────────────────────────────────────
#  HELPERS EXPRESIONES REGULARES
# ─────────────────────────────────────────────

def _er_union(a, b):
    if a is None:
        return b
    if b is None:
        return a
    if a == b:
        return a
    return f"({a}|{b})"

def _er_concat(a, b):
    if a is None or b is None:
        return None
    if a == "λ":
        return b
    if b == "λ":
        return a
    return f"{a}{b}"

def _necesita_paren(er):
    return "|" in er and not (er.startswith("(") and er.endswith(")"))

# ─────────────────────────────────────────────
#  CANVAS DE AUTÓMATA
# ─────────────────────────────────────────────

class AutomataCanvas(tk.Canvas):
    """Canvas interactivo para dibujar y editar autómatas."""

    R  = 28   # radio del círculo de estado
    AR = 10   # tamaño punta flecha

    def __init__(self, master, auto: Automata, on_change=None, readonly=False, **kw):
        super().__init__(master, bg=BG2, highlightthickness=0, **kw)
        self.auto       = auto
        self.on_change  = on_change
        self.readonly   = readonly
        self.pos        = {}     # nombre → (x, y)
        self.drag_data  = {}
        self.sel_state  = None
        self.mode       = "select"  # select | add_state | add_trans | delete
        self.trans_src  = None
        self.active_states = set()

        self.bind("<Button-1>",         self._click)
        self.bind("<B1-Motion>",        self._drag)
        self.bind("<ButtonRelease-1>",  self._release)
        self.bind("<Double-Button-1>",  self._dblclick)
        self.bind("<Button-3>",         self._rclick)
        self.bind("<Configure>",        lambda e: self.redraw())

    # ── Dibujo ──

    def redraw(self):
        self.delete("all")
        # Dibujar transiciones
        drawn = set()
        for src in self.auto.transitions:
            for sym in self.auto.transitions[src]:
                for dst in self.auto.transitions[src][sym]:
                    self._draw_edge(src, dst, sym, drawn)
        # Dibujar estados
        for name in self.auto.states:
            self._draw_state(name)

    def _draw_state(self, name):
        if name not in self.pos:
            self._auto_pos(name)
        x, y = self.pos[name]
        R    = self.R
        active   = name in self.active_states
        sel      = name == self.sel_state
        is_acc   = name in self.auto.accepting
        is_ini   = name == self.auto.initial

        fill  = ACTIVE if active else (STATE_ACC if is_acc else STATE_COL)
        outl  = "#ffffff" if sel else ("#f8fafc" if active else "#c7d2fe")
        width = 3 if sel or active else 1

        self.create_oval(x-R, y-R, x+R, y+R,
                         fill=fill, outline=outl, width=width, tags=("state", name))
        if is_acc:
            self.create_oval(x-R+5, y-R+5, x+R-5, y+R-5,
                             outline=outl, width=1, tags=("state", name))
        if is_ini:
            self.create_line(x-R-25, y, x-R, y,
                             arrow=tk.LAST, fill=STATE_INI, width=2)
        self.create_text(x, y, text=name, fill="#fff",
                         font=("Consolas", 9, "bold"), tags=("state", name))

    def _auto_pos(self, name):
        n = len(self.pos)
        w = self.winfo_width()  or 600
        h = self.winfo_height() or 400
        cx, cy = w//2, h//2
        r = min(w, h)//3
        angle = (2 * math.pi * n) / max(len(self.auto.states), 1)
        self.pos[name] = (cx + int(r * math.cos(angle)),
                          cy + int(r * math.sin(angle)))

    def _draw_edge(self, src, dst, sym, drawn):
        if src not in self.pos:
            self._auto_pos(src)
        if dst not in self.pos:
            self._auto_pos(dst)
        x1, y1 = self.pos[src]
        x2, y2 = self.pos[dst]
        R       = self.R

        # Agrupar etiquetas en la misma dirección
        key = (src, dst)
        rev = (dst, src)

        if src == dst:
            # Self-loop
            self.create_arc(x1-R-10, y1-R-30, x1+R+10, y1+R+10,
                            start=60, extent=240,
                            style=tk.ARC, outline=EDGE_COL, width=2)
            # Etiqueta
            etiq = self._get_edge_label(src, dst)
            self.create_text(x1, y1-R-18, text=etiq, fill=ACCENT2,
                             font=("Consolas", 8))
            drawn.add((src, dst))
            return

        if key in drawn:
            return
        drawn.add(key)
        drawn.add(rev)

        etiq_fwd = self._get_edge_label(src, dst)
        etiq_bwd = self._get_edge_label(dst, src)
        ambos    = etiq_bwd is not None

        dx, dy = x2-x1, y2-y1
        dist   = math.hypot(dx, dy) or 1
        ux, uy = dx/dist, dy/dist
        # Puntos del borde de los círculos
        sx, sy = x1 + ux*R, y1 + uy*R
        ex, ey = x2 - ux*R, y2 - uy*R

        if ambos:
            # Flecha curva con offset perpendicular
            perp = (-uy, ux)
            off  = 18
            mx   = (sx+ex)/2 + perp[0]*off
            my   = (sy+ey)/2 + perp[1]*off
            self.create_line(sx, sy, mx, my, ex, ey,
                             arrow=tk.LAST, smooth=True,
                             fill=EDGE_COL, width=2)
            self.create_text(mx, my, text=etiq_fwd, fill=ACCENT2,
                             font=("Consolas", 8))
            # Reversa
            mx2 = (sx+ex)/2 - perp[0]*off
            my2 = (sy+ey)/2 - perp[1]*off
            self.create_line(ex, ey, mx2, my2, sx, sy,
                             arrow=tk.LAST, smooth=True,
                             fill=EDGE_COL, width=2)
            self.create_text(mx2, my2, text=etiq_bwd, fill=ACCENT2,
                             font=("Consolas", 8))
        else:
            mx = (sx+ex)/2
            my = (sy+ey)/2
            self.create_line(sx, sy, ex, ey,
                             arrow=tk.LAST, fill=EDGE_COL, width=2)
            self.create_text(mx, my-8, text=etiq_fwd, fill=ACCENT2,
                             font=("Consolas", 8))

    def _get_edge_label(self, src, dst):
        syms = []
        for sym, dsts in self.auto.transitions[src].items():
            if dst in dsts:
                syms.append(sym)
        if not syms:
            return None
        return ",".join(sorted(syms))

    # ── Interacción ──

    def set_mode(self, mode):
        self.mode     = mode
        self.trans_src = None

    def _state_at(self, x, y):
        for name, (px, py) in self.pos.items():
            if math.hypot(x-px, y-py) <= self.R:
                return name
        return None

    def _click(self, e):
        if self.readonly:
            return
        hit = self._state_at(e.x, e.y)

        if self.mode == "select":
            self.sel_state = hit
            if hit:
                self.drag_data = {"name": hit, "x": e.x, "y": e.y}
            self.redraw()

        elif self.mode == "add_state":
            if not hit:
                name = simpledialog.askstring("Nuevo estado", "Nombre del estado:",
                                              parent=self.master)
                if name:
                    self.auto.add_state(name)
                    self.pos[name] = (e.x, e.y)
                    self._notify()
                    self.redraw()

        elif self.mode == "add_trans":
            if hit:
                if self.trans_src is None:
                    self.trans_src = hit
                    self.sel_state = hit
                    self.redraw()
                else:
                    sym = simpledialog.askstring("Transición",
                        f"Símbolo de '{self.trans_src}' → '{hit}'\n(usa λ para lambda):",
                        parent=self.master)
                    if sym is not None:
                        sym = sym.strip() or "λ"
                        self.auto.add_transition(self.trans_src, sym, hit)
                        self._notify()
                        self.redraw()
                    self.trans_src = None
                    self.sel_state = None

        elif self.mode == "delete":
            if hit:
                if messagebox.askyesno("Eliminar", f"¿Eliminar estado '{hit}'?"):
                    self.auto.remove_state(hit)
                    self.pos.pop(hit, None)
                    self._notify()
                    self.redraw()

    def _drag(self, e):
        if self.readonly or self.mode != "select":
            return
        if self.drag_data.get("name"):
            name = self.drag_data["name"]
            self.pos[name] = (e.x, e.y)
            self.redraw()

    def _release(self, e):
        self.drag_data = {}

    def _dblclick(self, e):
        if self.readonly:
            return
        hit = self._state_at(e.x, e.y)
        if hit and self.mode == "select":
            dlg = StatePropsDialog(self.master, hit, self.auto)
            self.master.wait_window(dlg)
            self.redraw()
            self._notify()

    def _rclick(self, e):
        if self.readonly:
            return
        hit = self._state_at(e.x, e.y)
        if hit:
            menu = tk.Menu(self, tearoff=0,
                           bg=BG3, fg=FG, activebackground=ACCENT)
            menu.add_command(label="Inicial", command=lambda: self._set_inicial(hit))
            menu.add_command(label="Aceptación", command=lambda: self._toggle_acc(hit))
            menu.add_command(label="Eliminar estado", command=lambda: self._del_state(hit))
            menu.post(e.x_root, e.y_root)

    def _set_inicial(self, name):
        self.auto.initial = name
        self.redraw()
        self._notify()

    def _toggle_acc(self, name):
        if name in self.auto.accepting:
            self.auto.accepting.discard(name)
        else:
            self.auto.accepting.add(name)
        self.redraw()
        self._notify()

    def _del_state(self, name):
        self.auto.remove_state(name)
        self.pos.pop(name, None)
        self.redraw()
        self._notify()

    def _notify(self):
        if self.on_change:
            self.on_change()

    def highlight(self, states):
        self.active_states = set(states)
        self.redraw()

    def load_automata(self, auto, pos=None):
        self.auto = auto
        self.pos  = pos or {}
        self.active_states = set()
        self.redraw()

    def auto_layout(self):
        """Distribuye estados en círculo."""
        n = len(self.auto.states)
        if n == 0:
            return
        w = self.winfo_width()  or 600
        h = self.winfo_height() or 400
        cx, cy = w//2, h//2
        r = min(w,h)//3
        for i, name in enumerate(self.auto.states):
            angle = (2 * math.pi * i) / n
            self.pos[name] = (cx + int(r * math.cos(angle)),
                              cy + int(r * math.sin(angle)))
        self.redraw()


# ─────────────────────────────────────────────
#  DIÁLOGO PROPIEDADES DE ESTADO
# ─────────────────────────────────────────────

class StatePropsDialog(tk.Toplevel):
    def __init__(self, parent, name, auto):
        super().__init__(parent)
        self.title(f"Estado: {name}")
        self.configure(bg=BG)
        self.resizable(False, False)
        self.auto = auto
        self.name = name

        ttk.Label(self, text=f"Estado: {name}",
                  style="H.TLabel").pack(pady=10, padx=20)

        v_ini = tk.BooleanVar(value=(auto.initial == name))
        v_acc = tk.BooleanVar(value=(name in auto.accepting))

        tk.Checkbutton(self, text="Estado inicial",
                       variable=v_ini, bg=BG, fg=FG,
                       selectcolor=BG3, activebackground=BG).pack(anchor="w", padx=20)
        tk.Checkbutton(self, text="Estado de aceptación",
                       variable=v_acc, bg=BG, fg=FG,
                       selectcolor=BG3, activebackground=BG).pack(anchor="w", padx=20)

        def aplicar():
            if v_ini.get():
                auto.initial = name
            elif auto.initial == name:
                auto.initial = None
            if v_acc.get():
                auto.accepting.add(name)
            else:
                auto.accepting.discard(name)
            self.destroy()

        btn_frame = tk.Frame(self, bg=BG)
        btn_frame.pack(pady=10)
        _btn(btn_frame, "Aplicar", aplicar).pack(side="left", padx=5)
        _btn(btn_frame, "Cancelar", self.destroy, red=True).pack(side="left", padx=5)


# ─────────────────────────────────────────────
#  HELPERS GUI
# ─────────────────────────────────────────────

def _btn(parent, text, cmd, red=False):
    color = RED if red else BTN_BG
    b = tk.Button(parent, text=text, command=cmd,
                  bg=color, fg=BTN_FG,
                  relief="flat", padx=10, pady=4,
                  activebackground=ACCENT2,
                  font=("Segoe UI", 9, "bold"),
                  cursor="hand2")
    return b

def _label(parent, text, big=False):
    size = 11 if big else 9
    return tk.Label(parent, text=text, bg=BG, fg=FG,
                    font=("Segoe UI", size))

def _entry(parent, width=20):
    e = tk.Entry(parent, width=width, bg=ENTRY_BG, fg=FG,
                 insertbackground=FG,
                 relief="flat", font=("Consolas", 10))
    return e

def _text(parent, h=8, w=40):
    t = tk.Text(parent, height=h, width=w, bg=ENTRY_BG, fg=FG,
                insertbackground=FG,
                relief="flat", font=("Consolas", 9),
                wrap="word")
    return t

def _scrolled_text(parent, h=8, w=40):
    frame = tk.Frame(parent, bg=BG2)
    t = _text(frame, h, w)
    sb = tk.Scrollbar(frame, command=t.yview, bg=BG3,
                      troughcolor=BG2, relief="flat")
    t.configure(yscrollcommand=sb.set)
    t.pack(side="left", fill="both", expand=True)
    sb.pack(side="right", fill="y")
    return frame, t

def _mostrar(widget, lista):
    widget.config(state="normal")
    widget.delete("1.0", tk.END)
    for item in lista:
        widget.insert(tk.END, item + "\n")
    widget.config(state="disabled")

def _guardar_txt(widget, nombre):
    contenido = widget.get("1.0", tk.END).strip()
    if not contenido:
        messagebox.showinfo("Vacío", "No hay datos para guardar")
        return
    path = filedialog.asksaveasfilename(
        defaultextension=".txt",
        initialfile=nombre + ".txt",
        filetypes=[("Texto", "*.txt")])
    if path:
        with open(path, "w", encoding="utf-8") as f:
            f.write(contenido)
        messagebox.showinfo("Guardado", "Archivo guardado correctamente")

# ─────────────────────────────────────────────
#  PANEL BARRA DE HERRAMIENTAS DE AUTÓMATA
# ─────────────────────────────────────────────

class AutomataToolbar(tk.Frame):
    """Barra de botones de modo de edición."""
    def __init__(self, parent, canvas: AutomataCanvas, extra_btns=None, **kw):
        super().__init__(parent, bg=BG3, **kw)
        self.canvas = canvas
        modos = [
            ("↖ Seleccionar", "select"),
            ("⊕ Añadir estado", "add_state"),
            ("→ Añadir transición", "add_trans"),
            ("✕ Eliminar", "delete"),
        ]
        for txt, mode in modos:
            b = tk.Button(self, text=txt,
                          command=lambda m=mode: canvas.set_mode(m),
                          bg=BG3, fg=FG, relief="flat",
                          activebackground=ACCENT,
                          font=("Segoe UI", 8), padx=6, pady=3,
                          cursor="hand2")
            b.pack(side="left", padx=2, pady=3)

        tk.Label(self, text="|", bg=BG3, fg=FG2).pack(side="left", padx=4)

        b2 = tk.Button(self, text="⟳ Auto-layout",
                       command=canvas.auto_layout,
                       bg=BG3, fg=FG, relief="flat",
                       activebackground=ACCENT,
                       font=("Segoe UI", 8), padx=6, pady=3,
                       cursor="hand2")
        b2.pack(side="left", padx=2, pady=3)

        if extra_btns:
            tk.Label(self, text="|", bg=BG3, fg=FG2).pack(side="left", padx=4)
            for txt, cmd in extra_btns:
                tk.Button(self, text=txt, command=cmd,
                          bg=BG3, fg=FG, relief="flat",
                          activebackground=ACCENT,
                          font=("Segoe UI", 8), padx=6, pady=3,
                          cursor="hand2").pack(side="left", padx=2, pady=3)


# ─────────────────────────────────────────────
#  TAB 1 – Subcadenas / Prefijos / Sufijos
# ─────────────────────────────────────────────

class TabCadenas(ttk.Frame):
    def __init__(self, nb):
        super().__init__(nb)
        self.configure(style="Dark.TFrame")
        self._build()

    def _build(self):
        top = tk.Frame(self, bg=BG)
        top.pack(fill="x", padx=10, pady=8)

        _label(top, "Cadena:").grid(row=0, column=0, padx=5)
        self.ent = _entry(top, 30)
        self.ent.grid(row=0, column=1, padx=5)

        self.vacia = tk.BooleanVar()
        tk.Checkbutton(top, text="Incluir λ",
                       variable=self.vacia,
                       bg=BG, fg=FG, selectcolor=BG3,
                       activebackground=BG).grid(row=0, column=2)

        _btn(top, "Calcular", self._calcular).grid(row=0, column=3, padx=10)

        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True, padx=10)

        cols = [("Prefijos", "pref"), ("Subcadenas", "sub"), ("Sufijos", "suf")]
        self.txts = {}
        for i, (titulo, key) in enumerate(cols):
            col = tk.Frame(body, bg=BG)
            col.grid(row=0, column=i, sticky="nsew", padx=5, pady=5)
            body.columnconfigure(i, weight=1)
            tk.Label(col, text=titulo, bg=BG, fg=ACCENT2,
                     font=("Segoe UI", 10, "bold")).pack()
            frame, txt = _scrolled_text(col, h=22, w=22)
            frame.pack(fill="both", expand=True)
            txt.config(state="disabled")
            self.txts[key] = txt
            _btn(col, f"💾 Guardar {titulo}",
                 lambda k=key, t=titulo: _guardar_txt(self.txts[k], t.lower())
                 ).pack(pady=4)

    def _calcular(self):
        cadena = self.ent.get()
        vacia  = self.vacia.get()
        _mostrar(self.txts["pref"], prefijos(cadena, vacia))
        _mostrar(self.txts["sub"],  subcadenas(cadena, vacia))
        _mostrar(self.txts["suf"],  sufijos(cadena, vacia))


# ─────────────────────────────────────────────
#  TAB 2 – Cerraduras
# ─────────────────────────────────────────────

class TabCerraduras(ttk.Frame):
    def __init__(self, nb):
        super().__init__(nb)
        self._build()

    def _build(self):
        top = tk.Frame(self, bg=BG)
        top.pack(fill="x", padx=10, pady=8)

        _label(top, "Alfabeto (ej: abc  o  a,b,c):").grid(row=0, column=0)
        self.alf = _entry(top, 20)
        self.alf.grid(row=0, column=1, padx=5)

        _label(top, "Long. máxima:").grid(row=0, column=2)
        self.n_ent = _entry(top, 5)
        self.n_ent.insert(0, "3")
        self.n_ent.grid(row=0, column=3, padx=5)

        _btn(top, "Generar", self._generar).grid(row=0, column=4, padx=10)

        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True, padx=10)

        self.txts = {}
        for i, (titulo, key) in enumerate([("Σ* (Kleene)", "star"), ("Σ+ (Positiva)", "plus")]):
            col = tk.Frame(body, bg=BG)
            col.grid(row=0, column=i, sticky="nsew", padx=5, pady=5)
            body.columnconfigure(i, weight=1)
            tk.Label(col, text=titulo, bg=BG, fg=ACCENT2,
                     font=("Segoe UI", 10, "bold")).pack()
            frame, txt = _scrolled_text(col, h=22, w=30)
            frame.pack(fill="both", expand=True)
            txt.config(state="disabled")
            self.txts[key] = txt
            _btn(col, f"💾 Guardar",
                 lambda k=key, t=titulo: _guardar_txt(self.txts[k], t)
                 ).pack(pady=4)

    def _generar(self):
        lista = parse_alfabeto(self.alf.get())
        try:
            n = int(self.n_ent.get())
        except ValueError:
            messagebox.showerror("Error", "Longitud máxima debe ser un número entero")
            return
        _mostrar(self.txts["star"], generar_kleene(lista, n, True))
        _mostrar(self.txts["plus"], generar_kleene(lista, n, False))


# ─────────────────────────────────────────────
#  TAB 3 – Editor / Simulador de Autómatas
# ─────────────────────────────────────────────

class TabAutomata(ttk.Frame):
    """
    Editor gráfico + simulación de AFD, AFND, AFN-λ.
    También minimización y conversión AFD → ER.
    """

    def __init__(self, nb):
        super().__init__(nb)
        self.auto = Automata()
        self._build()

    def _build(self):
        # ── Barra superior ──
        topbar = tk.Frame(self, bg=BG3)
        topbar.pack(fill="x")

        # Tipo de autómata
        tk.Label(topbar, text="Tipo:", bg=BG3, fg=FG,
                 font=("Segoe UI", 9)).pack(side="left", padx=(10, 2), pady=5)
        self.tipo_var = tk.StringVar(value="AFD")
        for t in ("AFD", "AFND", "AFN-λ"):
            tk.Radiobutton(topbar, text=t, variable=self.tipo_var, value=t,
                           bg=BG3, fg=FG, selectcolor=ACCENT,
                           activebackground=BG3,
                           command=self._cambiar_tipo,
                           font=("Segoe UI", 9)).pack(side="left", padx=3)

        sep = tk.Label(topbar, text="|", bg=BG3, fg=FG2)
        sep.pack(side="left", padx=6)

        for txt, cmd in [
            ("📂 Abrir .jff",   self._importar_jff),
            ("📂 Abrir .json",  self._abrir_json),
            ("💾 Guardar",      self._guardar),
            ("🗑 Limpiar",      self._limpiar),
        ]:
            _btn(topbar, txt, cmd).pack(side="left", padx=3, pady=5)

        # ── Panel principal ──
        paned = tk.PanedWindow(self, orient="horizontal",
                               bg=BG, sashwidth=6, sashpad=2)
        paned.pack(fill="both", expand=True)

        # — Canvas —
        left = tk.Frame(paned, bg=BG)
        paned.add(left, minsize=350)

        self.canvas = AutomataCanvas(left, self.auto,
                                     on_change=self._on_change,
                                     width=500, height=450)
        self.toolbar = AutomataToolbar(left, self.canvas)
        self.toolbar.pack(fill="x")
        self.canvas.pack(fill="both", expand=True, padx=5, pady=5)

        # — Panel derecho —
        right = tk.Frame(paned, bg=BG)
        paned.add(right, minsize=280)

        # Simulación
        sim_frame = tk.LabelFrame(right, text=" Simulación ",
                                   bg=BG, fg=ACCENT2,
                                   font=("Segoe UI", 9, "bold"),
                                   relief="flat", bd=1,
                                   highlightbackground=ACCENT,
                                   highlightthickness=1)
        sim_frame.pack(fill="x", padx=8, pady=8)

        row = tk.Frame(sim_frame, bg=BG)
        row.pack(fill="x", padx=6, pady=6)
        _label(row, "Cadena:").pack(side="left")
        self.sim_ent = _entry(row, 20)
        self.sim_ent.pack(side="left", padx=5)
        _btn(row, "▶ Simular", self._simular).pack(side="left")

        self.sim_result = tk.Label(sim_frame, text="",
                                   bg=BG, fg=FG,
                                   font=("Consolas", 10, "bold"))
        self.sim_result.pack(pady=4)

        sf, self.sim_log = _scrolled_text(sim_frame, h=6, w=32)
        sf.pack(fill="x", padx=6, pady=4)
        self.sim_log.config(state="disabled")

        # λ-clausura
        lc_frame = tk.LabelFrame(right, text=" λ-Clausura ",
                                  bg=BG, fg=ACCENT2,
                                  font=("Segoe UI", 9, "bold"),
                                  relief="flat", bd=1,
                                  highlightbackground=ACCENT,
                                  highlightthickness=1)
        lc_frame.pack(fill="x", padx=8, pady=4)

        row2 = tk.Frame(lc_frame, bg=BG)
        row2.pack(fill="x", padx=6, pady=6)
        _label(row2, "Estado:").pack(side="left")
        self.lc_ent = _entry(row2, 12)
        self.lc_ent.pack(side="left", padx=5)
        _btn(row2, "Calcular λ-clausura", self._lambda_clausura).pack(side="left")

        self.lc_result = tk.Label(lc_frame, text="", bg=BG, fg=ACCENT2,
                                   font=("Consolas", 9))
        self.lc_result.pack(pady=4)

        # Conversiones
        conv_frame = tk.LabelFrame(right, text=" Conversiones ",
                                    bg=BG, fg=ACCENT2,
                                    font=("Segoe UI", 9, "bold"),
                                    relief="flat", bd=1,
                                    highlightbackground=ACCENT,
                                    highlightthickness=1)
        conv_frame.pack(fill="x", padx=8, pady=4)

        for txt, cmd in [
            ("AFND/AFN-λ → AFD",  self._convertir_afd),
            ("Minimizar AFD",      self._minimizar),
            ("AFD → ER",           self._afd_a_er),
        ]:
            _btn(conv_frame, txt, cmd).pack(fill="x", padx=8, pady=3)

        # Info
        info_frame = tk.LabelFrame(right, text=" Info ",
                                    bg=BG, fg=ACCENT2,
                                    font=("Segoe UI", 9, "bold"),
                                    relief="flat", bd=1,
                                    highlightbackground=ACCENT,
                                    highlightthickness=1)
        info_frame.pack(fill="both", expand=True, padx=8, pady=4)

        if2, self.info_txt = _scrolled_text(info_frame, h=8, w=32)
        if2.pack(fill="both", expand=True, padx=4, pady=4)
        self.info_txt.config(state="disabled")

    # ── Callbacks ──

    def _cambiar_tipo(self):
        self.auto.tipo = self.tipo_var.get()

    def _on_change(self):
        self._update_info()

    def _update_info(self):
        a = self.auto
        lines = [
            f"Tipo: {a.tipo}",
            f"Estados ({len(a.states)}): {', '.join(a.states) or '—'}",
            f"Alfabeto: {', '.join(a.alphabet) or '—'}",
            f"Inicial: {a.initial or '—'}",
            f"Aceptación: {', '.join(sorted(a.accepting)) or '—'}",
            "",
            "Tabla de transiciones:",
        ]
        for s in a.states:
            for sym in sorted(a.transitions[s]):
                dsts = sorted(a.transitions[s][sym])
                lines.append(f"  δ({s},{sym}) = {{{','.join(dsts)}}}")
        _mostrar(self.info_txt, lines)

    def _simular(self):
        cadena = self.sim_ent.get()
        tipo   = self.auto.tipo

        if tipo == "AFD":
            acept, traza = self.auto.simular_afd(cadena)
            lines = []
            for i, (estado, sym) in enumerate(traza):
                if i == 0:
                    lines.append(f"Inicio: {estado}")
                else:
                    lines.append(f"  --{sym}--> {estado}")
            _mostrar(self.sim_log, lines)
            # Resaltar último estado
            if traza:
                self.canvas.highlight({traza[-1][0]})
        else:
            acept, pasos = self.auto.simular_nd(cadena)
            lines = []
            syms  = list(cadena)
            for i, conj in enumerate(pasos):
                if i == 0:
                    lines.append(f"Inicio: {{{','.join(sorted(conj))}}}")
                else:
                    lines.append(f"  --{syms[i-1]}--> {{{','.join(sorted(conj))}}}")
            _mostrar(self.sim_log, lines)
            if pasos:
                self.canvas.highlight(pasos[-1])

        color = GREEN if acept else RED
        texto = "✔ ACEPTADA" if acept else "✗ RECHAZADA"
        self.sim_result.config(text=texto, fg=color)

    def _lambda_clausura(self):
        est = self.lc_ent.get().strip()
        if est not in self.auto.states:
            messagebox.showerror("Error", f"Estado '{est}' no existe")
            return
        clausura = self.auto.lambda_clausura_single(est)
        self.lc_result.config(
            text=f"λ-clausura({est}) = {{{','.join(sorted(clausura))}}}")
        self.canvas.highlight(clausura)

    def _convertir_afd(self):
        afd = self.auto.a_afd()
        self._mostrar_en_ventana("AFD equivalente (método de subconjuntos)", afd)

    def _minimizar(self):
        if self.auto.tipo != "AFD":
            messagebox.showerror("Error", "Solo se puede minimizar un AFD")
            return
        min_afd, grupos = self.auto.minimizar()
        info  = "Grupos de equivalencia:\n"
        for g in grupos:
            info += f"  {{{','.join(sorted(g))}}}\n"
        info += f"\nEstados antes: {len(self.auto.states)}\n"
        info += f"Estados después: {len(min_afd.states)}\n"
        self._mostrar_en_ventana("AFD Minimizado", min_afd, extra_info=info)

    def _afd_a_er(self):
        if self.auto.tipo != "AFD":
            messagebox.showerror("Error", "Solo se puede convertir un AFD")
            return
        if not self.auto.initial:
            messagebox.showerror("Error", "El AFD necesita estado inicial")
            return
        er, pasos = self.auto.afd_a_er()
        ERDialog(self, er, pasos)

    def _mostrar_en_ventana(self, titulo, auto, extra_info=""):
        win = tk.Toplevel(self)
        win.title(titulo)
        win.configure(bg=BG)
        win.geometry("720x520")

        if extra_info:
            tk.Label(win, text=extra_info, bg=BG, fg=ACCENT2,
                     font=("Consolas", 9), justify="left").pack(padx=10, pady=5, anchor="w")

        canvas = AutomataCanvas(win, auto, readonly=True,
                                width=700, height=420)
        canvas.pack(fill="both", expand=True, padx=5, pady=5)
        canvas.after(100, canvas.auto_layout)

    def _importar_jff(self):
        path = filedialog.askopenfilename(
            filetypes=[("JFLAP", "*.jff"), ("Todos", "*.*")])
        if not path:
            return
        try:
            self.auto = Automata.desde_jff(path)
            self.tipo_var.set(self.auto.tipo)
            self.canvas.load_automata(self.auto, {})
            self.canvas.after(100, self.canvas.auto_layout)
            self._update_info()
            messagebox.showinfo("Importado", f"AFD importado: {os.path.basename(path)}")
        except Exception as exc:
            messagebox.showerror("Error al importar", str(exc))

    def _abrir_json(self):
        path = filedialog.askopenfilename(
            filetypes=[("JSON", "*.json"), ("Todos", "*.*")])
        if not path:
            return
        try:
            self.auto = Automata.desde_json(path)
            self.tipo_var.set(self.auto.tipo)
            self.canvas.load_automata(self.auto, {})
            self.canvas.after(100, self.canvas.auto_layout)
            self._update_info()
        except Exception as exc:
            messagebox.showerror("Error", str(exc))

    def _guardar(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json")])
        if path:
            self.auto.guardar_json(path)
            messagebox.showinfo("Guardado", "Autómata guardado correctamente")

    def _limpiar(self):
        if messagebox.askyesno("Limpiar", "¿Eliminar el autómata actual?"):
            self.auto.reset()
            self.canvas.pos = {}
            self.canvas.load_automata(self.auto)
            self._update_info()


# ─────────────────────────────────────────────
#  DIÁLOGO ER – muestra la conversión AFD→ER
# ─────────────────────────────────────────────

class ERDialog(tk.Toplevel):
    def __init__(self, parent, er, pasos):
        super().__init__(parent)
        self.title("Conversión AFD → ER (eliminación de estados)")
        self.configure(bg=BG)
        self.geometry("600x480")

        tk.Label(self, text="Expresión Regular resultante:",
                 bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 10, "bold")).pack(pady=(12, 2))

        er_box = tk.Entry(self, font=("Consolas", 13, "bold"),
                          bg=ENTRY_BG, fg=GREEN,
                          readonlybackground=ENTRY_BG,
                          state="readonly",
                          relief="flat")
        er_box.pack(fill="x", padx=20, pady=4)
        er_box.config(state="normal")
        er_box.insert(0, er)
        er_box.config(state="readonly")

        tk.Label(self, text="Pasos de eliminación:",
                 bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 9, "bold")).pack(pady=(8, 0), padx=10, anchor="w")

        frame, txt = _scrolled_text(self, h=16, w=70)
        frame.pack(fill="both", expand=True, padx=10, pady=6)

        lineas = []
        for i, (desc, er_paso) in enumerate(pasos, 1):
            lineas.append(f"Paso {i}: {desc}")
            lineas.append(f"  ER actual: {er_paso}")
            lineas.append("")
        _mostrar(txt, lineas)

        _btn(self, "Cerrar", self.destroy).pack(pady=8)


# ─────────────────────────────────────────────
#  TAB 4 – Validadores con Expresiones Regulares
# ─────────────────────────────────────────────

VALIDATORS = {
    "Correo electrónico": (
        r'^[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}$',
        "nombre@dominio.ext",
        "ejemplo: user@escom.ipn.mx"
    ),
    "Teléfono (México)": (
        r'^(\+52[\s\-]?)?(\(?\d{2,3}\)?[\s\-]?)?\d{4}[\s\-]?\d{4}$',
        "55-1234-5678  o  +52 55 1234 5678",
        "formato nacional o internacional"
    ),
    "URL": (
        r'^(https?|ftp):\/\/([\w\-]+(\.[\w\-]+)+)([\w\-\._~:/?#\[\]@!$&\'()*+,;=%]*)?$',
        "https://www.ejemplo.com/ruta",
        "debe incluir protocolo http/https"
    ),
    "Fecha (DD/MM/AAAA o DD-MM-AAAA)": (
        r'^(0[1-9]|[12]\d|3[01])([\/\-])(0[1-9]|1[0-2])\2(\d{4})$',
        "31/12/2024  o  31-12-2024",
        "DD/MM/AAAA o DD-MM-AAAA"
    ),
    "Contraseña segura": (
        r'^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&_\-])[A-Za-z\d@$!%*?&_\-]{8,}$',
        "Min 8 chars, mayúscula, minúscula, dígito y símbolo especial",
        "ej: MiClave@123"
    ),
}

class TabValidadores(ttk.Frame):
    def __init__(self, nb):
        super().__init__(nb)
        self._build()

    def _build(self):
        top = tk.Frame(self, bg=BG)
        top.pack(fill="x", padx=10, pady=8)

        _label(top, "Tipo de validación:").pack(side="left")
        self.tipo_var = tk.StringVar(value=list(VALIDATORS.keys())[0])
        combo = ttk.Combobox(top, textvariable=self.tipo_var,
                              values=list(VALIDATORS.keys()),
                              width=32, state="readonly",
                              font=("Segoe UI", 9))
        combo.pack(side="left", padx=8)
        combo.bind("<<ComboboxSelected>>", self._update_hint)

        body = tk.Frame(self, bg=BG)
        body.pack(fill="both", expand=True, padx=15, pady=5)

        # ER usada
        tk.Label(body, text="Expresión regular:", bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")
        self.er_txt = tk.Text(body, height=2, width=70,
                               bg=ENTRY_BG, fg=ACCENT2,
                               font=("Consolas", 9), relief="flat",
                               wrap="word", state="disabled")
        self.er_txt.pack(fill="x", pady=4)

        # Hint
        self.hint_lbl = tk.Label(body, text="", bg=BG, fg=FG2,
                                  font=("Segoe UI", 9, "italic"))
        self.hint_lbl.pack(anchor="w")

        # Entrada
        row = tk.Frame(body, bg=BG)
        row.pack(fill="x", pady=8)
        tk.Label(row, text="Texto a validar:", bg=BG, fg=FG,
                 font=("Segoe UI", 9)).pack(side="left")
        self.ent = _entry(row, 45)
        self.ent.pack(side="left", padx=8)
        _btn(row, "✔ Validar", self._validar).pack(side="left")
        self.ent.bind("<Return>", lambda e: self._validar())

        # Resultado
        self.res_lbl = tk.Label(body, text="",
                                 bg=BG, fg=FG,
                                 font=("Consolas", 14, "bold"))
        self.res_lbl.pack(pady=4)

        self.det_lbl = tk.Label(body, text="",
                                 bg=BG, fg=FG2,
                                 font=("Segoe UI", 9),
                                 wraplength=600, justify="left")
        self.det_lbl.pack(anchor="w")

        # Prueba múltiple
        sep = tk.Frame(body, bg=BG3, height=1)
        sep.pack(fill="x", pady=12)

        tk.Label(body, text="Validación múltiple (una cadena por línea):",
                 bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")

        bf, self.batch_in = _scrolled_text(body, h=5, w=60)
        bf.pack(fill="x", pady=4)

        _btn(body, "▶ Validar todas", self._batch).pack(pady=4)

        rf, self.batch_out = _scrolled_text(body, h=6, w=60)
        rf.pack(fill="both", expand=True, pady=4)
        self.batch_out.config(state="disabled")

        self._update_hint()

    def _update_hint(self, *_):
        tipo = self.tipo_var.get()
        if tipo not in VALIDATORS:
            return
        pattern, ejemplo, hint = VALIDATORS[tipo]
        self.er_txt.config(state="normal")
        self.er_txt.delete("1.0", tk.END)
        self.er_txt.insert("1.0", pattern)
        self.er_txt.config(state="disabled")
        self.hint_lbl.config(text=f"Formato: {ejemplo}  —  {hint}")

    def _validar(self):
        tipo    = self.tipo_var.get()
        pattern, _, _ = VALIDATORS[tipo]
        texto   = self.ent.get()
        if re.match(pattern, texto):
            self.res_lbl.config(text="✔ VÁLIDO", fg=GREEN)
            self.det_lbl.config(text=f"'{texto}' cumple el patrón.")
        else:
            self.res_lbl.config(text="✗ INVÁLIDO", fg=RED)
            self.det_lbl.config(text=self._sugerencia(tipo, texto))

    def _batch(self):
        tipo    = self.tipo_var.get()
        pattern, _, _ = VALIDATORS[tipo]
        lineas  = self.batch_in.get("1.0", tk.END).strip().split("\n")
        results = []
        for l in lineas:
            l = l.strip()
            if not l:
                continue
            ok = "✔" if re.match(pattern, l) else "✗"
            results.append(f"{ok}  {l}")
        _mostrar(self.batch_out, results)

    def _sugerencia(self, tipo, texto):
        tips = {
            "Correo electrónico":           "¿Falta el '@' o el dominio?",
            "Teléfono (México)":            "Prueba formato: 55-1234-5678 o +52 55 1234 5678",
            "URL":                          "Asegúrate de incluir http:// o https://",
            "Fecha (DD/MM/AAAA o DD-MM-AAAA)": "Formato esperado: DD/MM/AAAA, ej: 31/12/2024",
            "Contraseña segura":            "Necesita ≥8 chars, mayúscula, minúscula, dígito y símbolo (@$!%*?&)",
        }
        return tips.get(tipo, "El texto no cumple el patrón.")


# ─────────────────────────────────────────────
#  TAB 5 – Ayuda / Investigación
# ─────────────────────────────────────────────

AYUDA = """
╔══════════════════════════════════════════════════════════════════╗
║        TEORÍA DE LA COMPUTACIÓN – ESCOM IPN                    ║
╚══════════════════════════════════════════════════════════════════╝

━━━ EXPRESIONES REGULARES ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Definición formal de LENGUAJE REGULAR:
  Un lenguaje L sobre Σ es regular si existe un AFD M tal que L = L(M).
  Equivalentemente, puede describirse con una expresión regular.

Componentes básicos de una ER:
  • ∅         — lenguaje vacío
  • λ (ε)     — cadena vacía
  • a ∈ Σ     — símbolo del alfabeto
  • (R₁|R₂)  — unión: cadenas en R₁ o en R₂
  • (R₁R₂)   — concatenación: cadena de R₁ seguida de una de R₂
  • (R*)      — Cierre de Kleene: cero o más repeticiones de R

Jerarquía de Chomsky:
  Tipo 0 – Irrestrictos (Máquinas de Turing)
  Tipo 1 – Sensibles al contexto (Autómatas linealmente acotados)
  Tipo 2 – Libres de contexto (APD)
  Tipo 3 – REGULARES (AFD / AFND / ER)  ← estamos aquí

Teorema de Kleene:
  ER ←→ AFND ←→ AFD
  Todo lenguaje descrito por una ER tiene un AFD equivalente y viceversa.

━━━ MÉTODOS DE CONVERSIÓN AFD → ER ━━━━━━━━━━━━━━━━━━━━━━━━━━━━

1. Eliminación de estados (GNFA):
   Agregar qi y qf, eliminar estados intermedios uno a uno,
   actualizando etiquetas de arcos. La ER queda en el arco qi→qf.

2. Método de ecuaciones (Arden):
   Plantear un sistema de ecuaciones lineales de la forma
   Qi = Σ_{a∈Σ} a·Q_{δ(i,a)}  +  (λ si es final)
   Resolver usando el Lema de Arden: X = AX|B  ⟹  X = A*B

3. Método de Arden:
   Variante directa del anterior.  Particularmente útil en AFD pequeños.

━━━ APLICACIONES PRÁCTICAS DE EXPRESIONES REGULARES ━━━━━━━━━━━

1. VALIDACIÓN DE FORMULARIOS WEB
   ^[a-zA-Z0-9._%+\\-]+@[a-zA-Z0-9.\\-]+\\.[a-zA-Z]{2,}$
   Verifica correos electrónicos en tiempo real.

2. ANÁLISIS LÉXICO EN COMPILADORES
   Herramientas como Lex/Flex usan ER para tokenizar código fuente:
   identificadores: [a-zA-Z_][a-zA-Z0-9_]*
   números:         [0-9]+(\\.[0-9]+)?

3. BÚSQUEDA DE PATRONES EN TEXTO (grep, sed, awk)
   grep -E '^(ERROR|WARN).*2024' log.txt
   Filtra líneas de error/advertencia en logs.

4. FILTRADO DE DATOS (ETL, limpieza de datasets)
   Eliminar caracteres no deseados, normalizar formatos de fechas,
   extraer información estructurada de texto libre.

5. AUTOMATIZACIÓN EN SISTEMAS OPERATIVOS
   find . -regex '.*\\.py$'   — buscar todos los archivos Python
   rename 's/IMG_/foto_/g' *  — renombrar archivos en masa.

━━━ SIMULACIÓN DE AUTÓMATAS ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

AFD  – Cada par (estado, símbolo) tiene exactamente una transición.
AFND – Un par puede tener cero, una o varias transiciones.
AFN-λ– Igual que AFND más transiciones λ (sin consumir símbolo).

λ-clausura(q) = conjunto de estados alcanzables desde q
                usando solo transiciones λ.

Minimización (Hopcroft):
  1. Eliminar estados inaccesibles.
  2. Particionar en {aceptación} y {no-aceptación}.
  3. Refinar partición hasta estabilidad.
  4. Construir AFD mínimo con representantes de cada clase.

━━━ USO DEL SOFTWARE ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Pestaña "Cadenas":   Prefijos, sufijos, subcadenas, cerraduras.
Pestaña "Cerraduras": Σ* y Σ+ hasta longitud n.
Pestaña "Autómata":  Editor gráfico interactivo.
  • Haz clic derecho sobre un estado para marcarlo inicial/final.
  • Doble clic para editar propiedades.
  • Importa .jff desde JFLAP con 📂 Abrir .jff
  • Simula cadenas y observa el recorrido paso a paso.
  • Convierte AFND→AFD, Minimiza AFD, genera ER.
Pestaña "Validadores": Prueba expresiones regulares reales.
"""

class TabAyuda(ttk.Frame):
    def __init__(self, nb):
        super().__init__(nb)
        t = tk.Text(self, bg=BG, fg=FG,
                    font=("Consolas", 9),
                    wrap="word", relief="flat",
                    padx=20, pady=10)
        sb = tk.Scrollbar(self, command=t.yview, bg=BG3, relief="flat")
        t.configure(yscrollcommand=sb.set)
        t.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        t.insert("1.0", AYUDA)
        t.config(state="disabled")


# ─────────────────────────────────────────────
#  VENTANA PRINCIPAL
# ─────────────────────────────────────────────

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Teoría de la Computación – ESCOM IPN")
        self.geometry("1100x700")
        self.configure(bg=BG)

        self._apply_styles()

        # Encabezado
        header = tk.Frame(self, bg=ACCENT, height=42)
        header.pack(fill="x")
        tk.Label(header,
                 text="  ⚙  Teoría de la Computación  |  ESCOM – IPN",
                 bg=ACCENT, fg="#fff",
                 font=("Segoe UI", 11, "bold")).pack(side="left", padx=10)
        tk.Label(header, text="Prácticas 1–4",
                 bg=ACCENT, fg="#d1d5db",
                 font=("Segoe UI", 9)).pack(side="right", padx=12)

        # Notebook
        self.nb = ttk.Notebook(self, style="Dark.TNotebook")
        self.nb.pack(fill="both", expand=True, padx=0, pady=0)

        self.nb.add(TabCadenas(self.nb),    text="  📝 Cadenas  ")
        self.nb.add(TabCerraduras(self.nb), text="  Σ*/Σ+  ")
        self.nb.add(TabAutomata(self.nb),   text="  🤖 Autómata  ")
        self.nb.add(TabValidadores(self.nb),text="  ✔ Validadores ER  ")
        self.nb.add(TabAyuda(self.nb),      text="  ❓ Ayuda / Teoría  ")

    def _apply_styles(self):
        style = ttk.Style(self)
        style.theme_use("clam")
        style.configure("Dark.TNotebook",
                         background=BG, borderwidth=0)
        style.configure("Dark.TNotebook.Tab",
                         background=BG3, foreground=FG,
                         padding=[12, 5],
                         font=("Segoe UI", 9, "bold"))
        style.map("Dark.TNotebook.Tab",
                  background=[("selected", ACCENT)],
                  foreground=[("selected", "#fff")])
        style.configure("Dark.TFrame", background=BG)
        style.configure("TFrame",      background=BG)
        style.configure("TLabel",      background=BG, foreground=FG)
        style.configure("H.TLabel",    background=BG, foreground=ACCENT2,
                         font=("Segoe UI", 10, "bold"))
        style.configure("TCombobox",   fieldbackground=ENTRY_BG,
                         background=ENTRY_BG, foreground=FG,
                         selectbackground=ACCENT)


if __name__ == "__main__":
    app = App()
    app.mainloop()
