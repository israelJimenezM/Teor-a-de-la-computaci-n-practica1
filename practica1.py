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
#  PRÁCTICA 5 – GRAMÁTICAS (FNC / FNG)
# ─────────────────────────────────────────────

class GramaticaGIC:
    """
    Gramática Independiente del Contexto.
    Almacena producciones como dict: Variable -> list[tuple[str,...]]
    Cada símbolo es un str (mayúscula = variable, minúscula/otro = terminal).
    """

    def __init__(self):
        self.variables  = []   # ordenadas
        self.terminales = []
        self.inicial    = None
        self.producciones = {}  # {V: [ [símbolo,...], ... ]}

    # ── Parser ──────────────────────────────────────────────────────────────

    @staticmethod
    def parsear(texto):
        """
        Lee texto con formato:
            S -> aB | b | λ
            A -> aA | a
        Devuelve un GramaticaGIC o lanza ValueError.
        """
        g = GramaticaGIC()
        lineas = [l.strip() for l in texto.strip().splitlines() if l.strip()]
        if not lineas:
            raise ValueError("Gramática vacía")

        for linea in lineas:
            if "->" not in linea:
                raise ValueError(f"Línea sin '->': {linea}")
            izq, der = linea.split("->", 1)
            lhs = izq.strip()
            if not lhs:
                raise ValueError("Lado izquierdo vacío")
            if lhs not in g.variables:
                g.variables.append(lhs)
            if g.inicial is None:
                g.inicial = lhs
            alternativas = der.split("|")
            for alt in alternativas:
                alt = alt.strip()
                if not alt:
                    continue
                produccion = GramaticaGIC._tokenizar(alt)
                g.producciones.setdefault(lhs, []).append(produccion)

        # Detectar terminales
        for var, prods in g.producciones.items():
            for prod in prods:
                for sym in prod:
                    if sym not in g.variables and sym != "λ" and sym != "ε":
                        if sym not in g.terminales:
                            g.terminales.append(sym)
        return g

    @staticmethod
    def _tokenizar(alt):
        """Divide la cadena en símbolos: cada mayúscula seguida de dígitos es
        una variable; el resto char por char son terminales."""
        tokens = []
        i = 0
        while i < len(alt):
            if alt[i].isupper():
                j = i + 1
                while j < len(alt) and (alt[j].isdigit() or alt[j] == "'"):
                    j += 1
                tokens.append(alt[i:j])
                i = j
            elif alt[i] == 'λ' or alt[i] == 'ε':
                tokens.append("λ")
                i += 1
            else:
                tokens.append(alt[i])
                i += 1
        return tokens if tokens else ["λ"]

    def copia(self):
        g = GramaticaGIC()
        g.variables   = list(self.variables)
        g.terminales  = list(self.terminales)
        g.inicial     = self.inicial
        g.producciones = {v: [list(p) for p in prods]
                          for v, prods in self.producciones.items()}
        return g

    def to_str(self):
        lineas = []
        for v in self.variables:
            prods = self.producciones.get(v, [])
            rhs = " | ".join("".join(p) for p in prods) if prods else "∅"
            lineas.append(f"{v} -> {rhs}")
        return "\n".join(lineas)


# ── Algoritmos FNC ────────────────────────────────────────────────────────────

def _fnc_nueva_var(base, existentes):
    """Genera un nombre de variable nuevo no existente."""
    i = 1
    while True:
        nombre = f"{base}{i}"
        if nombre not in existentes:
            return nombre
        i += 1

def fnc_transformar(g_orig):
    """
    Transforma g_orig a Forma Normal de Chomsky.
    Devuelve (GramaticaGIC_fnc, lista_de_pasos_str).
    """
    pasos = []
    g = g_orig.copia()

    # ── Paso 0: nuevo símbolo inicial si el inicial aparece en algún lado derecho
    inicial_en_rhs = any(
        g.inicial in prod
        for var, prods in g.producciones.items()
        for prod in prods
    )
    if inicial_en_rhs:
        s0 = _fnc_nueva_var("S", g.variables)
        g.variables.insert(0, s0)
        g.producciones[s0] = [[g.inicial]]
        g.inicial = s0
        pasos.append(f"Paso 0 – Nuevo símbolo inicial: {s0} -> {g.producciones[s0][0][0]}")
    else:
        pasos.append("Paso 0 – Símbolo inicial no aparece en RHS, no se agrega nuevo inicial.")

    # ── Paso 1: Eliminar producciones λ ──────────────────────────────────────
    # Calcular anulables
    anulables = set()
    cambiado = True
    while cambiado:
        cambiado = False
        for v, prods in g.producciones.items():
            if v in anulables:
                continue
            for prod in prods:
                if prod == ["λ"] or all(s in anulables for s in prod):
                    anulables.add(v)
                    cambiado = True
    pasos.append(f"Paso 1 – Anulables: {{{', '.join(sorted(anulables))}}}")

    # Expandir producciones eliminando λ combinatoriamente
    nuevas = {}
    for v, prods in g.producciones.items():
        conj = set()
        for prod in prods:
            if prod == ["λ"]:
                continue  # se elimina
            # generar todas las combinaciones quitando anulables
            anulables_idx = [i for i, s in enumerate(prod) if s in anulables]
            for r in range(len(anulables_idx) + 1):
                for combo in itertools.combinations(anulables_idx, r):
                    nueva = [s for i, s in enumerate(prod) if i not in combo]
                    if nueva:
                        conj.add(tuple(nueva))
        nuevas[v] = [list(p) for p in conj] if conj else [["λ"]]
    # Mantener λ solo para el inicial si era anulable
    if g.inicial in anulables:
        nuevas[g.inicial].append(["λ"])
    g.producciones = nuevas
    pasos.append("Paso 1 – Producciones λ eliminadas (excepto S0 -> λ si aplica).")

    # ── Paso 2: Eliminar producciones unitarias ───────────────────────────────
    # Para cada variable calcular clausura unitaria
    def clausura_unitaria(v):
        visitados = {v}
        cola = [v]
        while cola:
            u = cola.pop()
            for prod in g.producciones.get(u, []):
                if len(prod) == 1 and prod[0] in g.variables and prod[0] not in visitados:
                    visitados.add(prod[0])
                    cola.append(prod[0])
        return visitados

    nuevas2 = {}
    for v in g.variables:
        conj = set()
        for u in clausura_unitaria(v):
            for prod in g.producciones.get(u, []):
                if not (len(prod) == 1 and prod[0] in g.variables):
                    conj.add(tuple(prod))
        nuevas2[v] = [list(p) for p in conj] if conj else []
    g.producciones = nuevas2
    pasos.append("Paso 2 – Producciones unitarias eliminadas.")

    # ── Paso 3: Eliminar símbolos inútiles ───────────────────────────────────
    # 3a: generadores
    generadores = set(g.terminales) | {"λ"}
    cambiado = True
    while cambiado:
        cambiado = False
        for v, prods in g.producciones.items():
            if v in generadores:
                continue
            for prod in prods:
                if all(s in generadores for s in prod):
                    generadores.add(v)
                    cambiado = True
                    break
    utiles_gen = generadores & set(g.variables)
    # 3b: alcanzables
    alcanzables = {g.inicial}
    cola = [g.inicial]
    while cola:
        v = cola.pop()
        for prod in g.producciones.get(v, []):
            for s in prod:
                if s in g.variables and s not in alcanzables:
                    alcanzables.add(s)
                    cola.append(s)
    utiles = utiles_gen & alcanzables
    g.variables = [v for v in g.variables if v in utiles]
    g.producciones = {
        v: [p for p in prods if all(s in utiles or s in g.terminales or s == "λ" for s in p)]
        for v, prods in g.producciones.items() if v in utiles
    }
    pasos.append(f"Paso 3 – Símbolos útiles: {{{', '.join(g.variables)}}}")

    # ── Paso 4: Convertir a FNC propiamente ──────────────────────────────────
    # 4a: reemplazar terminales en producciones de longitud >= 2
    term_var = {}   # terminal -> variable auxiliar
    nuevas4 = {v: list(prods) for v, prods in g.producciones.items()}

    def conseguir_var_terminal(t):
        if t not in term_var:
            nv = _fnc_nueva_var("T" + t.upper() if t.isalpha() else "TX", g.variables)
            term_var[t] = nv
            g.variables.append(nv)
            nuevas4[nv] = [[t]]
        return term_var[t]

    for v in list(nuevas4):
        prods_mod = []
        for prod in nuevas4[v]:
            if len(prod) >= 2:
                nueva = []
                for s in prod:
                    if s in g.terminales:
                        nueva.append(conseguir_var_terminal(s))
                    else:
                        nueva.append(s)
                prods_mod.append(nueva)
            else:
                prods_mod.append(prod)
        nuevas4[v] = prods_mod
    g.producciones = nuevas4

    # 4b: romper producciones de longitud > 2
    nuevas5 = {v: [] for v in g.variables}
    for v in list(g.variables):
        for prod in g.producciones.get(v, []):
            actual = prod
            src = v
            while len(actual) > 2:
                # crear nueva variable
                nv = _fnc_nueva_var("D", g.variables)
                g.variables.append(nv)
                nuevas5[nv] = []
                nuevas5[src].append([actual[0], nv])
                actual = actual[1:]
                src = nv
            nuevas5[src].append(actual)
    # Actualizar terminales
    g.terminales = list(set(
        s for prods in nuevas5.values()
        for p in prods for s in p
        if s not in g.variables and s != "λ"
    ))
    g.producciones = nuevas5
    pasos.append("Paso 4 – Producciones convertidas a FNC (máx 2 símbolos, terminales separados).")
    pasos.append("\n✔ Transformación a FNC completada.")
    return g, pasos


# ── Algoritmos FNG ────────────────────────────────────────────────────────────

def fng_transformar(g_orig):
    """
    Transforma g_orig a Forma Normal de Greibach (primer símbolo terminal).
    Devuelve (GramaticaGIC_fng, lista_de_pasos_str).
    Requiere que la gramática ya esté en FNC o sin λ-producciones.
    Usa el método estándar: eliminar recursión izquierda + sustitución.
    """
    pasos = []
    # Primero llevar a FNC para garantizar punto de partida limpio
    g_fnc, pasos_fnc = fnc_transformar(g_orig)
    pasos.append("[Aplicando FNC como base para FNG...]")
    pasos.extend(pasos_fnc)
    pasos.append("")
    g = g_fnc.copia()

    # Asignar orden a las variables: la inicial primero
    orden = [g.inicial] + [v for v in g.variables if v != g.inicial]

    # ── Eliminar recursión izquierda directa e indirecta ──────────────────────
    for i, Ai in enumerate(orden):
        # Sustituir Aj (j < i) en producciones de Ai
        for j in range(i):
            Aj = orden[j]
            nuevas_prods = []
            for prod in g.producciones.get(Ai, []):
                if prod and prod[0] == Aj:
                    # sustituir Aj por sus producciones
                    for prod_j in g.producciones.get(Aj, []):
                        nuevas_prods.append(prod_j + prod[1:])
                else:
                    nuevas_prods.append(prod)
            g.producciones[Ai] = nuevas_prods
            pasos.append(f"FNG: sustituir {Aj} en {Ai}")

        # Eliminar recursión izquierda directa en Ai
        recursivas = [p for p in g.producciones.get(Ai, []) if p and p[0] == Ai]
        no_recursivas = [p for p in g.producciones.get(Ai, []) if not (p and p[0] == Ai)]

        if recursivas:
            Bi = _fnc_nueva_var(Ai + "'", g.variables)
            g.variables.append(Bi)
            # Ai -> α | αBi  para cada α en no-recursivas
            nuevas_ai = []
            for alpha in no_recursivas:
                nuevas_ai.append(alpha)
                nuevas_ai.append(alpha + [Bi])
            g.producciones[Ai] = nuevas_ai
            # Bi -> β | βBi  para cada Ai->Aiβ
            prods_bi = []
            for beta in [p[1:] for p in recursivas]:
                prods_bi.append(beta)
                prods_bi.append(beta + [Bi])
            g.producciones[Bi] = prods_bi
            pasos.append(f"FNG: recursión izquierda en {Ai} eliminada, nuevo símbolo {Bi}")

    orden = [g.inicial] + [v for v in g.variables if v != g.inicial]

    # ── Garantizar que todas las producciones empiecen con terminal ───────────
    # Para variables en orden inverso, sustituir
    for i in range(len(orden) - 1, -1, -1):
        Ai = orden[i]
        nuevas_prods = []
        for prod in g.producciones.get(Ai, []):
            if prod and prod[0] in g.variables:
                # sustituir la cabeza
                cabeza_var = prod[0]
                resto = prod[1:]
                for prod_cabeza in g.producciones.get(cabeza_var, []):
                    nuevas_prods.append(prod_cabeza + resto)
            else:
                nuevas_prods.append(prod)
        g.producciones[Ai] = nuevas_prods

    pasos.append("\n✔ Transformación a FNG completada (primer símbolo siempre terminal).")
    return g, pasos


class TabGramaticas(ttk.Frame):
    """Pestaña Práctica 5: Transformación de gramáticas a FNC y FNG."""

    def __init__(self, nb):
        super().__init__(nb)
        self.configure(style="Dark.TFrame")
        self._build()

    def _build(self):
        # ── Panel izquierdo: entrada y acciones ───────────────────────────────
        main = tk.PanedWindow(self, orient="horizontal",
                              bg=BG, sashwidth=6)
        main.pack(fill="both", expand=True)

        left = tk.Frame(main, bg=BG)
        main.add(left, minsize=320)

        right = tk.Frame(main, bg=BG)
        main.add(right, minsize=400)

        # ── Entrada ──────────────────────────────────────────────────────────
        tk.Label(left, text="Gramática GIC",
                 bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 10, "bold")).pack(pady=(10, 2), padx=10, anchor="w")
        tk.Label(left,
                 text="Formato: S -> aB | λ   (una variable por línea)",
                 bg=BG, fg=FG2, font=("Segoe UI", 8, "italic")
                 ).pack(padx=10, anchor="w")

        ef, self.gram_txt = _scrolled_text(left, h=14, w=36)
        ef.pack(fill="x", padx=10, pady=6)

        # Cargar ejemplo
        ejemplo = "S -> aSb | AB\nA -> aA | a\nB -> bB | b"
        self.gram_txt.insert("1.0", ejemplo)

        btn_row = tk.Frame(left, bg=BG)
        btn_row.pack(fill="x", padx=10, pady=4)
        _btn(btn_row, "📐 → FNC", self._a_fnc).pack(side="left", padx=4)
        _btn(btn_row, "📏 → FNG", self._a_fng).pack(side="left", padx=4)
        _btn(btn_row, "🗑 Limpiar", self._limpiar).pack(side="left", padx=4)

        # Resultado actual
        tk.Label(left, text="Gramática transformada:",
                 bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 9, "bold")).pack(padx=10, pady=(12, 2), anchor="w")
        rf, self.result_txt = _scrolled_text(left, h=10, w=36)
        rf.pack(fill="x", padx=10, pady=4)
        self.result_txt.config(state="disabled")
        _btn(left, "💾 Guardar resultado",
             lambda: _guardar_txt(self.result_txt, "gramatica_transformada")
             ).pack(pady=4)

        # ── Panel derecho: log de pasos ───────────────────────────────────────
        tk.Label(right, text="Pasos de transformación",
                 bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 10, "bold")).pack(pady=(10, 2), padx=10, anchor="w")
        lf, self.log_txt = _scrolled_text(right, h=40, w=55)
        lf.pack(fill="both", expand=True, padx=10, pady=6)
        self.log_txt.config(state="disabled")
        _btn(right, "💾 Guardar pasos",
             lambda: _guardar_txt(self.log_txt, "pasos_transformacion")
             ).pack(pady=4)

    def _parsear(self):
        texto = self.gram_txt.get("1.0", tk.END).strip()
        try:
            return GramaticaGIC.parsear(texto)
        except ValueError as e:
            messagebox.showerror("Error al parsear gramática", str(e))
            return None

    def _a_fnc(self):
        g = self._parsear()
        if g is None:
            return
        try:
            g_fnc, pasos = fnc_transformar(g)
            self._mostrar_resultado(g_fnc, pasos, "FNC")
        except Exception as e:
            messagebox.showerror("Error FNC", str(e))

    def _a_fng(self):
        g = self._parsear()
        if g is None:
            return
        try:
            g_fng, pasos = fng_transformar(g)
            self._mostrar_resultado(g_fng, pasos, "FNG")
        except Exception as e:
            messagebox.showerror("Error FNG", str(e))

    def _mostrar_resultado(self, g, pasos, tipo):
        self.result_txt.config(state="normal")
        self.result_txt.delete("1.0", tk.END)
        self.result_txt.insert(tk.END, f"=== Gramática en {tipo} ===\n\n")
        self.result_txt.insert(tk.END, g.to_str())
        self.result_txt.config(state="disabled")

        log_lines = [f"=== Pasos de transformación a {tipo} ===", ""]
        log_lines.extend(pasos)
        log_lines.extend(["", "=== Gramática resultante ===", "", g.to_str()])
        _mostrar(self.log_txt, log_lines)

    def _limpiar(self):
        self.gram_txt.delete("1.0", tk.END)
        self.result_txt.config(state="normal")
        self.result_txt.delete("1.0", tk.END)
        self.result_txt.config(state="disabled")
        self.log_txt.config(state="normal")
        self.log_txt.delete("1.0", tk.END)
        self.log_txt.config(state="disabled")


# ─────────────────────────────────────────────
#  PRÁCTICA 6 – AUTÓMATA DE PILA (PDA)
# ─────────────────────────────────────────────

class PDA:
    """
    Autómata de Pila No Determinista.
    Transiciones: δ(estado, símbolo|λ, tope_pila) → {(nuevo_estado, cadena_pila), ...}
    Acepta por estado final.
    """

    def __init__(self):
        self.reset()

    def reset(self):
        self.states        = []
        self.alphabet      = []      # Σ (sin λ)
        self.stack_alphabet = []     # Γ
        self.initial       = None
        self.initial_stack  = "Z"   # Símbolo inicial de pila
        self.accepting     = set()
        self.transitions   = defaultdict(lambda: defaultdict(lambda: defaultdict(set)))
        # transitions[estado][sym_entrada][sym_pila] = {(nuevo_estado, cadena_pila_push), ...}

    def add_state(self, name, initial=False, accepting=False):
        if name not in self.states:
            self.states.append(name)
        if initial:
            self.initial = name
        if accepting:
            self.accepting.add(name)

    def add_transition(self, src, sym_in, sym_stack, dst, push_str):
        """
        sym_in   : símbolo de entrada o 'λ'
        sym_stack: tope de pila que se consume
        push_str : cadena que se apila (izq=tope). 'λ' = pop sin push.
        """
        self.transitions[src][sym_in][sym_stack].add((dst, push_str))
        if sym_in not in self.alphabet and sym_in != "λ":
            self.alphabet.append(sym_in)
        if sym_stack not in self.stack_alphabet and sym_stack != "λ":
            self.stack_alphabet.append(sym_stack)
        if push_str not in self.stack_alphabet and push_str not in ("λ", ""):
            for c in push_str:
                if c not in self.stack_alphabet:
                    self.stack_alphabet.append(c)

    def remove_state(self, name):
        if name in self.states:
            self.states.remove(name)
        if self.initial == name:
            self.initial = None
        self.accepting.discard(name)
        self.transitions.pop(name, None)

    # ── Simulación ────────────────────────────────────────────────────────────

    def simular(self, cadena, max_pasos=500):
        """
        Simula el PDA sobre 'cadena'.
        Devuelve (aceptada, pasos) donde cada paso es
        (estado, símbolo_leído, pila_actual, acción).
        """
        if self.initial is None:
            return False, []

        # Configuración: (estado, idx_cadena, pila_tuple)
        init_stack = (self.initial_stack,)
        init_cfg   = (self.initial, 0, init_stack)
        visitados  = set()
        cola_bfs   = [(init_cfg, [(self.initial, "inicio", list(init_stack), "-")])]
        pasos_result = None
        aceptada     = False

        while cola_bfs and max_pasos > 0:
            max_pasos -= 1
            cfg, historial = cola_bfs.pop(0)
            estado, idx, pila = cfg

            key = (estado, idx, pila)
            if key in visitados:
                continue
            visitados.add(key)

            # Verificar aceptación
            if idx == len(cadena) and estado in self.accepting:
                aceptada     = True
                pasos_result = historial
                break

            # Obtener símbolo de entrada
            sym_in = cadena[idx] if idx < len(cadena) else None
            tope   = pila[-1] if pila else None

            if tope is None:
                continue

            # Transiciones con símbolo
            if sym_in:
                for sym_s, dests in self.transitions[estado][sym_in].items():
                    if sym_s == tope or sym_s == "λ":
                        for (dst, push) in dests:
                            nueva_pila = list(pila[:-1])
                            if push != "λ" and push != "":
                                nueva_pila.extend(reversed(push))
                            accion = f"δ({estado},{sym_in},{sym_s})→({dst},{push})"
                            nuevo_hist = historial + [
                                (dst, sym_in, nueva_pila, accion)
                            ]
                            cola_bfs.append((
                                (dst, idx + 1, tuple(nueva_pila)),
                                nuevo_hist
                            ))

            # Transiciones λ (sin consumir entrada)
            for sym_s, dests in self.transitions[estado]["λ"].items():
                if sym_s == tope or sym_s == "λ":
                    for (dst, push) in dests:
                        nueva_pila = list(pila[:-1])
                        if push != "λ" and push != "":
                            nueva_pila.extend(reversed(push))
                        accion = f"δ({estado},λ,{sym_s})→({dst},{push})"
                        nuevo_hist = historial + [
                            (dst, "λ", nueva_pila, accion)
                        ]
                        cola_bfs.append((
                            (dst, idx, tuple(nueva_pila)),
                            nuevo_hist
                        ))

        if not aceptada:
            # Devolver el historial más largo encontrado para diagnóstico
            if cola_bfs:
                pasos_result = cola_bfs[-1][1]
            else:
                pasos_result = [(self.initial, "inicio", [self.initial_stack], "-")]
        return aceptada, pasos_result or []

    def guardar_json(self, path):
        trans_serial = {}
        for s, by_in in self.transitions.items():
            trans_serial[s] = {}
            for si, by_stack in by_in.items():
                trans_serial[s][si] = {}
                for ss, dests in by_stack.items():
                    trans_serial[s][si][ss] = list(dests)
        data = {
            "states":        self.states,
            "alphabet":      self.alphabet,
            "stack_alphabet": self.stack_alphabet,
            "initial":       self.initial,
            "initial_stack": self.initial_stack,
            "accepting":     list(self.accepting),
            "transitions":   trans_serial,
        }
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    @staticmethod
    def desde_json(path):
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        pda = PDA()
        pda.states         = data["states"]
        pda.alphabet       = data["alphabet"]
        pda.stack_alphabet = data["stack_alphabet"]
        pda.initial        = data["initial"]
        pda.initial_stack  = data.get("initial_stack", "Z")
        pda.accepting      = set(data["accepting"])
        for s, by_in in data["transitions"].items():
            for si, by_stack in by_in.items():
                for ss, dests in by_stack.items():
                    for d in dests:
                        pda.transitions[s][si][ss].add(tuple(d))
        return pda


class StackCanvas(tk.Canvas):
    """Visualización gráfica de una pila como rectángulos apilados."""

    ITEM_H = 30
    ITEM_W = 80

    def __init__(self, master, **kw):
        super().__init__(master, bg=BG2, highlightthickness=0, **kw)
        self._stack = []

    def mostrar(self, pila):
        """Recibe la pila como lista (índice 0 = fondo, -1 = tope)."""
        self._stack = list(pila)
        self.redraw()

    def redraw(self):
        self.delete("all")
        w = self.winfo_width()  or 120
        h = self.winfo_height() or 300
        n = len(self._stack)

        # Calcular posición base (parte inferior del canvas)
        base_y = h - 20
        cx     = w // 2
        hw     = self.ITEM_W // 2
        item_h = self.ITEM_H

        # Etiqueta «tope»
        if n > 0:
            self.create_text(cx, base_y - n * item_h - 14,
                             text="▼ tope", fill=ACCENT2,
                             font=("Segoe UI", 8, "italic"))

        for i, sym in enumerate(self._stack):
            # i=0 es fondo, i=n-1 es tope
            y2 = base_y - i * item_h
            y1 = y2 - item_h
            is_top = (i == n - 1)
            color  = ACCENT if is_top else BG3
            outl   = ACCENT2 if is_top else FG2

            self.create_rectangle(cx - hw, y1, cx + hw, y2,
                                  fill=color, outline=outl, width=2)
            self.create_text(cx, (y1 + y2) // 2, text=sym,
                             fill="#fff", font=("Consolas", 10, "bold"))

        # Fondo / base
        self.create_rectangle(cx - hw - 4, base_y, cx + hw + 4, base_y + 6,
                              fill=FG2, outline=FG2)
        self.create_text(cx, base_y + 14, text="fondo",
                         fill=FG2, font=("Segoe UI", 7))

        # Si vacía
        if n == 0:
            self.create_text(cx, h // 2, text="(vacía)",
                             fill=FG2, font=("Segoe UI", 9, "italic"))


class TabPDA(ttk.Frame):
    """Pestaña Práctica 6: Autómata de Pila (PDA)."""

    def __init__(self, nb):
        super().__init__(nb)
        self.pda = PDA()
        self._pasos   = []
        self._paso_idx = 0
        self._build()

    def _build(self):
        # ── Barra superior ────────────────────────────────────────────────────
        topbar = tk.Frame(self, bg=BG3)
        topbar.pack(fill="x")

        for txt, cmd in [
            ("💾 Guardar PDA",  self._guardar),
            ("📂 Abrir PDA",    self._abrir),
            ("🗑 Limpiar",      self._limpiar),
        ]:
            _btn(topbar, txt, cmd).pack(side="left", padx=3, pady=5)

        tk.Label(topbar, text="|", bg=BG3, fg=FG2).pack(side="left", padx=4)
        tk.Label(topbar, text="Símbolo inicial pila:",
                 bg=BG3, fg=FG,
                 font=("Segoe UI", 9)).pack(side="left")
        self.init_stack_var = tk.StringVar(value="Z")
        e_is = tk.Entry(topbar, textvariable=self.init_stack_var,
                        width=4, bg=ENTRY_BG, fg=FG,
                        insertbackground=FG, relief="flat",
                        font=("Consolas", 10))
        e_is.pack(side="left", padx=4)

        # ── Layout principal ──────────────────────────────────────────────────
        main = tk.PanedWindow(self, orient="horizontal",
                              bg=BG, sashwidth=6)
        main.pack(fill="both", expand=True)

        # Columna izq: canvas del autómata + toolbar
        left = tk.Frame(main, bg=BG)
        main.add(left, minsize=340)

        # Reutilizamos AutomataCanvas para visualizar PDA
        # Creamos un Automata espejo que refleja los estados del PDA
        self._auto_mirror = Automata()
        self.canvas = AutomataCanvas(left, self._auto_mirror,
                                     on_change=self._sync_canvas,
                                     width=480, height=420)
        self.toolbar = AutomataToolbar(left, self.canvas)
        self.toolbar.pack(fill="x")
        self.canvas.pack(fill="both", expand=True, padx=5, pady=5)

        # Columna der: controles + pila
        right = tk.Frame(main, bg=BG)
        main.add(right, minsize=380)

        # Columna der se divide: panel de transiciones + simulación | pila
        der_paned = tk.PanedWindow(right, orient="horizontal",
                                   bg=BG, sashwidth=5)
        der_paned.pack(fill="both", expand=True)

        ctrl = tk.Frame(der_paned, bg=BG)
        der_paned.add(ctrl, minsize=240)

        stack_frame = tk.Frame(der_paned, bg=BG)
        der_paned.add(stack_frame, minsize=120)

        # ── Panel de transiciones ─────────────────────────────────────────────
        trans_lf = tk.LabelFrame(ctrl, text=" Agregar Transición ",
                                  bg=BG, fg=ACCENT2,
                                  font=("Segoe UI", 9, "bold"),
                                  relief="flat", bd=1,
                                  highlightbackground=ACCENT,
                                  highlightthickness=1)
        trans_lf.pack(fill="x", padx=6, pady=6)

        fields = [
            ("Estado origen:",    "t_src"),
            ("Símbolo entrada:",  "t_in"),
            ("Tope de pila:",     "t_stack"),
            ("Estado destino:",   "t_dst"),
            ("Push en pila:",     "t_push"),
        ]
        self._t_entries = {}
        for i, (lbl, key) in enumerate(fields):
            tk.Label(trans_lf, text=lbl, bg=BG, fg=FG,
                     font=("Segoe UI", 8)).grid(row=i, column=0, sticky="w",
                                                padx=6, pady=2)
            e = tk.Entry(trans_lf, width=14, bg=ENTRY_BG, fg=FG,
                         insertbackground=FG, relief="flat",
                         font=("Consolas", 9))
            e.grid(row=i, column=1, padx=6, pady=2)
            self._t_entries[key] = e

        hint = tk.Label(trans_lf,
                        text="Push: 'AB'=apila A sobre B | 'λ'=solo pop",
                        bg=BG, fg=FG2, font=("Segoe UI", 7, "italic"),
                        wraplength=220, justify="left")
        hint.grid(row=len(fields), column=0, columnspan=2, padx=6, pady=2)
        _btn(trans_lf, "➕ Agregar", self._agregar_trans).grid(
            row=len(fields)+1, column=0, columnspan=2, pady=6)

        # Lista de transiciones
        t_list_lf = tk.LabelFrame(ctrl, text=" Transiciones del PDA ",
                                   bg=BG, fg=ACCENT2,
                                   font=("Segoe UI", 9, "bold"),
                                   relief="flat", bd=1,
                                   highlightbackground=ACCENT,
                                   highlightthickness=1)
        t_list_lf.pack(fill="x", padx=6, pady=4)
        tlf, self.trans_list = _scrolled_text(t_list_lf, h=7, w=30)
        tlf.pack(fill="x", padx=4, pady=4)
        self.trans_list.config(state="disabled")

        # ── Simulación ────────────────────────────────────────────────────────
        sim_lf = tk.LabelFrame(ctrl, text=" Simulación ",
                                bg=BG, fg=ACCENT2,
                                font=("Segoe UI", 9, "bold"),
                                relief="flat", bd=1,
                                highlightbackground=ACCENT,
                                highlightthickness=1)
        sim_lf.pack(fill="x", padx=6, pady=6)

        row0 = tk.Frame(sim_lf, bg=BG)
        row0.pack(fill="x", padx=6, pady=4)
        _label(row0, "Cadena:").pack(side="left")
        self.sim_ent = _entry(row0, 18)
        self.sim_ent.pack(side="left", padx=4)

        btn_row = tk.Frame(sim_lf, bg=BG)
        btn_row.pack(fill="x", padx=6, pady=2)
        _btn(btn_row, "▶ Simular",   self._simular).pack(side="left", padx=2)
        _btn(btn_row, "⏮ Inicio",    self._paso_inicio).pack(side="left", padx=2)
        _btn(btn_row, "⬅ Anterior",  self._paso_ant).pack(side="left", padx=2)
        _btn(btn_row, "➡ Siguiente", self._paso_sig).pack(side="left", padx=2)

        self.sim_result = tk.Label(sim_lf, text="",
                                   bg=BG, fg=FG,
                                   font=("Consolas", 10, "bold"))
        self.sim_result.pack(pady=2)

        # Log de pasos
        slf, self.sim_log = _scrolled_text(ctrl, h=8, w=34)
        slf.pack(fill="both", expand=True, padx=6, pady=4)
        self.sim_log.config(state="disabled")

        # ── Stack canvas ──────────────────────────────────────────────────────
        tk.Label(stack_frame, text="Pila",
                 bg=BG, fg=ACCENT2,
                 font=("Segoe UI", 10, "bold")).pack(pady=(8, 2))
        self.stack_cv = StackCanvas(stack_frame, width=120)
        self.stack_cv.pack(fill="both", expand=True, padx=4, pady=4)

        # Inicializar pila vacía
        self.stack_cv.after(100, lambda: self.stack_cv.mostrar([]))

    # ── Helpers ───────────────────────────────────────────────────────────────

    def _sync_canvas(self):
        """Cuando el canvas edita estados, sincronizar con el PDA."""
        for name in self._auto_mirror.states:
            ini = (name == self._auto_mirror.initial)
            acc = (name in self._auto_mirror.accepting)
            self.pda.add_state(name, initial=ini, accepting=acc)
        self.pda.initial = self._auto_mirror.initial
        self.pda.accepting = set(self._auto_mirror.accepting)
        self._update_trans_list()

    def _agregar_trans(self):
        src   = self._t_entries["t_src"].get().strip()
        sym_i = self._t_entries["t_in"].get().strip()  or "λ"
        sym_s = self._t_entries["t_stack"].get().strip() or "λ"
        dst   = self._t_entries["t_dst"].get().strip()
        push  = self._t_entries["t_push"].get().strip() or "λ"

        if not src or not dst:
            messagebox.showerror("Error", "Ingresa estado origen y destino")
            return

        # Agregar estados al mirror si no existen
        if src not in self._auto_mirror.states:
            self._auto_mirror.add_state(src)
            self.canvas.auto_layout()
        if dst not in self._auto_mirror.states:
            self._auto_mirror.add_state(dst)
            self.canvas.auto_layout()

        # Agregar al espejo (etiqueta resumida en el canvas)
        etiq = f"{sym_i},{sym_s}/{push}"
        self._auto_mirror.add_transition(src, etiq, dst)
        self.canvas.redraw()

        # Agregar al PDA real
        self.pda.add_state(src)
        self.pda.add_state(dst)
        self.pda.initial_stack = self.init_stack_var.get().strip() or "Z"
        self.pda.add_transition(src, sym_i, sym_s, dst, push)
        self._update_trans_list()

    def _update_trans_list(self):
        lineas = []
        for s, by_in in self.pda.transitions.items():
            for si, by_stack in by_in.items():
                for ss, dests in by_stack.items():
                    for (d, push) in dests:
                        lineas.append(f"δ({s},{si},{ss}) → ({d},{push})")
        self.trans_list.config(state="normal")
        self.trans_list.delete("1.0", tk.END)
        for l in lineas:
            self.trans_list.insert(tk.END, l + "\n")
        self.trans_list.config(state="disabled")

    def _simular(self):
        self.pda.initial_stack = self.init_stack_var.get().strip() or "Z"
        if self._auto_mirror.initial:
            self.pda.initial = self._auto_mirror.initial
        self.pda.accepting  = set(self._auto_mirror.accepting)
        cadena = self.sim_ent.get()
        aceptada, pasos = self.pda.simular(cadena)
        self._pasos    = pasos
        self._paso_idx = 0

        color = GREEN if aceptada else RED
        texto = "✔ ACEPTADA" if aceptada else "✗ RECHAZADA"
        self.sim_result.config(text=texto, fg=color)

        self._mostrar_log()
        self._mostrar_paso()

    def _mostrar_log(self):
        lineas = [f"Total de pasos: {len(self._pasos)}", ""]
        for i, (est, sym, pila, acc) in enumerate(self._pasos):
            lineas.append(f"Paso {i:2d}: {acc}")
            lineas.append(f"        Estado: {est}  Pila: [{','.join(pila)}]")
        _mostrar(self.sim_log, lineas)

    def _mostrar_paso(self):
        if not self._pasos:
            return
        idx = max(0, min(self._paso_idx, len(self._pasos) - 1))
        est, sym, pila, accion = self._pasos[idx]
        self.canvas.highlight({est})
        self.stack_cv.mostrar(pila)
        # Resaltar línea en log
        self.sim_log.config(state="normal")
        self.sim_log.tag_remove("activo", "1.0", tk.END)
        line_no = idx * 2 + 3   # aprox
        self.sim_log.tag_add("activo", f"{line_no}.0", f"{line_no}.end")
        self.sim_log.tag_config("activo", background=ACCENT, foreground="#fff")
        self.sim_log.see(f"{line_no}.0")
        self.sim_log.config(state="disabled")

    def _paso_inicio(self):
        self._paso_idx = 0
        self._mostrar_paso()

    def _paso_ant(self):
        if self._paso_idx > 0:
            self._paso_idx -= 1
            self._mostrar_paso()

    def _paso_sig(self):
        if self._paso_idx < len(self._pasos) - 1:
            self._paso_idx += 1
            self._mostrar_paso()

    def _guardar(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json")])
        if path:
            try:
                self.pda.guardar_json(path)
                messagebox.showinfo("Guardado", "PDA guardado correctamente")
            except Exception as e:
                messagebox.showerror("Error", str(e))

    def _abrir(self):
        path = filedialog.askopenfilename(
            filetypes=[("JSON", "*.json"), ("Todos", "*.*")])
        if not path:
            return
        try:
            self.pda = PDA.desde_json(path)
            self.init_stack_var.set(self.pda.initial_stack)
            # Reconstruir mirror
            self._auto_mirror = Automata()
            for s in self.pda.states:
                ini = (s == self.pda.initial)
                acc = (s in self.pda.accepting)
                self._auto_mirror.add_state(s, initial=ini, accepting=acc)
            for s, by_in in self.pda.transitions.items():
                for si, by_stack in by_in.items():
                    for ss, dests in by_stack.items():
                        for (d, push) in dests:
                            etiq = f"{si},{ss}/{push}"
                            self._auto_mirror.add_transition(s, etiq, d)
            self.canvas.load_automata(self._auto_mirror)
            self.canvas.after(100, self.canvas.auto_layout)
            self._update_trans_list()
            messagebox.showinfo("Abierto", f"PDA cargado: {os.path.basename(path)}")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def _limpiar(self):
        if messagebox.askyesno("Limpiar", "¿Eliminar el PDA actual?"):
            self.pda.reset()
            self._auto_mirror = Automata()
            self.canvas.load_automata(self._auto_mirror)
            self._pasos    = []
            self._paso_idx = 0
            self._update_trans_list()
            self.sim_result.config(text="")
            self.stack_cv.mostrar([])
            self.sim_log.config(state="normal")
            self.sim_log.delete("1.0", tk.END)
            self.sim_log.config(state="disabled")



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
        tk.Label(header, text="Prácticas 1–6",
                 bg=ACCENT, fg="#d1d5db",
                 font=("Segoe UI", 9)).pack(side="right", padx=12)

        # Notebook
        self.nb = ttk.Notebook(self, style="Dark.TNotebook")
        self.nb.pack(fill="both", expand=True, padx=0, pady=0)

        self.nb.add(TabCadenas(self.nb),    text="  📝 Cadenas  ")
        self.nb.add(TabCerraduras(self.nb), text="  Σ*/Σ+  ")
        self.nb.add(TabAutomata(self.nb),   text="  🤖 Autómata  ")
        self.nb.add(TabValidadores(self.nb),text="  ✔ Validadores ER  ")
        self.nb.add(TabGramaticas(self.nb), text="  📐 Gramáticas  ")
        self.nb.add(TabPDA(self.nb),        text="  🥞 Aut. de Pila  ")
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
