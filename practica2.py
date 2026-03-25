"""
AFD Simulator - Simulador de Autómatas Finitos Deterministas
Desarrollado con Python + Flet
Funcionalidades: Creación, Importación, Simulación, Exportación, Subcadenas, Kleene
"""

import flet as ft
import json
import xml.etree.ElementTree as ET
import os
import re
from itertools import product as itertools_product
from typing import Optional

# ─────────────────────────────────────────────
#  MODELO DE DATOS
# ─────────────────────────────────────────────

class AFD:
    def __init__(self):
        self.states: list[str] = []
        self.alphabet: list[str] = []
        self.initial_state: Optional[str] = None
        self.accept_states: list[str] = []
        # transitions[state][symbol] = next_state
        self.transitions: dict[str, dict[str, str]] = {}

    def clear(self):
        self.__init__()

    def add_state(self, name: str):
        if name not in self.states:
            self.states.append(name)
            self.transitions[name] = {}

    def remove_state(self, name: str):
        if name in self.states:
            self.states.remove(name)
            self.transitions.pop(name, None)
            for s in self.transitions:
                for sym in list(self.transitions[s]):
                    if self.transitions[s][sym] == name:
                        del self.transitions[s][sym]
            if self.initial_state == name:
                self.initial_state = None
            if name in self.accept_states:
                self.accept_states.remove(name)

    def set_transition(self, from_state: str, symbol: str, to_state: str):
        if from_state in self.transitions:
            self.transitions[from_state][symbol] = to_state

    def validate(self, string: str) -> tuple[bool, list[tuple[str, str, str]]]:
        """Returns (accepted, trace) where trace = [(state, symbol, next_state), ...]"""
        if self.initial_state is None:
            return False, []
        current = self.initial_state
        trace = []
        for ch in string:
            if ch not in self.alphabet:
                return False, trace
            nxt = self.transitions.get(current, {}).get(ch)
            if nxt is None:
                trace.append((current, ch, "DEAD"))
                return False, trace
            trace.append((current, ch, nxt))
            current = nxt
        accepted = current in self.accept_states
        return accepted, trace

    def is_valid_definition(self) -> tuple[bool, str]:
        if not self.states:
            return False, "No hay estados definidos."
        if not self.alphabet:
            return False, "No hay alfabeto definido."
        if self.initial_state is None:
            return False, "No hay estado inicial definido."
        if not self.accept_states:
            return False, "No hay estados de aceptación definidos."
        return True, "OK"

    # ── Exportación ──────────────────────────────
    def to_jff(self) -> str:
        root = ET.Element("structure")
        ET.SubElement(root, "type").text = "fa"
        automaton = ET.SubElement(root, "automaton")
        for i, s in enumerate(self.states):
            node = ET.SubElement(automaton, "state", id=str(i), name=s)
            if s == self.initial_state:
                ET.SubElement(node, "initial")
            if s in self.accept_states:
                ET.SubElement(node, "final")
            ET.SubElement(node, "x").text = str(100 + i * 120)
            ET.SubElement(node, "y").text = "200"
        for frm, syms in self.transitions.items():
            for sym, to in syms.items():
                tr = ET.SubElement(automaton, "transition")
                ET.SubElement(tr, "from").text = str(self.states.index(frm))
                ET.SubElement(tr, "to").text = str(self.states.index(to))
                ET.SubElement(tr, "read").text = sym
        ET.indent(root, space="  ")
        return ET.tostring(root, encoding="unicode", xml_declaration=True)

    def to_json(self) -> str:
        data = {
            "alphabet": self.alphabet,
            "states": self.states,
            "initial_state": self.initial_state,
            "accept_states": self.accept_states,
            "transitions": self.transitions
        }
        return json.dumps(data, indent=2, ensure_ascii=False)

    def to_xml(self) -> str:
        root = ET.Element("afd")
        alph = ET.SubElement(root, "alphabet")
        for sym in self.alphabet:
            ET.SubElement(alph, "symbol").text = sym
        sts = ET.SubElement(root, "states")
        for s in self.states:
            node = ET.SubElement(sts, "state", name=s)
            if s == self.initial_state:
                node.set("initial", "true")
            if s in self.accept_states:
                node.set("accept", "true")
        trans = ET.SubElement(root, "transitions")
        for frm, syms in self.transitions.items():
            for sym, to in syms.items():
                tr = ET.SubElement(trans, "transition")
                tr.set("from", frm)
                tr.set("symbol", sym)
                tr.set("to", to)
        ET.indent(root, space="  ")
        return ET.tostring(root, encoding="unicode", xml_declaration=True)

    # ── Importación ──────────────────────────────
    @staticmethod
    def from_jff(content: str) -> "AFD":
        afd = AFD()
        root = ET.fromstring(content)
        automaton = root.find("automaton")
        id_to_name = {}
        for state in automaton.findall("state"):
            sid = state.get("id")
            name = state.get("name")
            id_to_name[sid] = name
            afd.add_state(name)
            if state.find("initial") is not None:
                afd.initial_state = name
            if state.find("final") is not None:
                afd.accept_states.append(name)
        for tr in automaton.findall("transition"):
            frm = id_to_name.get(tr.find("from").text, "")
            to = id_to_name.get(tr.find("to").text, "")
            read_el = tr.find("read")
            sym = read_el.text if read_el is not None and read_el.text else ""
            if sym and sym not in afd.alphabet:
                afd.alphabet.append(sym)
            if frm and to and sym:
                afd.set_transition(frm, sym, to)
        return afd

    @staticmethod
    def from_json(content: str) -> "AFD":
        afd = AFD()
        data = json.loads(content)
        afd.alphabet = data.get("alphabet", [])
        for s in data.get("states", []):
            afd.add_state(s)
        afd.initial_state = data.get("initial_state")
        afd.accept_states = data.get("accept_states", [])
        for frm, syms in data.get("transitions", {}).items():
            for sym, to in syms.items():
                afd.set_transition(frm, sym, to)
        return afd

    @staticmethod
    def from_xml(content: str) -> "AFD":
        afd = AFD()
        root = ET.fromstring(content)
        for sym in root.findall("./alphabet/symbol"):
            if sym.text:
                afd.alphabet.append(sym.text)
        for st in root.findall("./states/state"):
            name = st.get("name")
            afd.add_state(name)
            if st.get("initial") == "true":
                afd.initial_state = name
            if st.get("accept") == "true":
                afd.accept_states.append(name)
        for tr in root.findall("./transitions/transition"):
            frm = tr.get("from")
            sym = tr.get("symbol")
            to = tr.get("to")
            if frm and sym and to:
                afd.set_transition(frm, sym, to)
        return afd


# ─────────────────────────────────────────────
#  UTILIDADES DE CADENAS
# ─────────────────────────────────────────────

def get_prefixes(s: str) -> list[str]:
    return [s[:i] for i in range(len(s) + 1)]

def get_suffixes(s: str) -> list[str]:
    return [s[i:] for i in range(len(s) + 1)]

def get_substrings(s: str) -> list[str]:
    subs = set()
    for i in range(len(s)):
        for j in range(i, len(s) + 1):
            subs.add(s[i:j])
    return sorted(subs)

def kleene_star(alphabet: list[str], max_len: int) -> list[str]:
    results = [""]
    for length in range(1, max_len + 1):
        for combo in itertools_product(alphabet, repeat=length):
            results.append("".join(combo))
    return results

def kleene_plus(alphabet: list[str], max_len: int) -> list[str]:
    results = []
    for length in range(1, max_len + 1):
        for combo in itertools_product(alphabet, repeat=length):
            results.append("".join(combo))
    return results


# ─────────────────────────────────────────────
#  APLICACIÓN FLET
# ─────────────────────────────────────────────

DARK_BG    = "#0d0f14"
PANEL_BG   = "#13161e"
CARD_BG    = "#1a1e2a"
BORDER     = "#2a2f3d"
ACCENT     = "#5b8af5"
ACCENT2    = "#a78bfa"
SUCCESS    = "#34d399"
DANGER     = "#f87171"
TEXT       = "#e2e8f0"
TEXT_MUTED = "#6b7280"
FONT_MONO  = "Courier New"


def make_chip(label: str, color: str = ACCENT) -> ft.Container:
    return ft.Container(
        content=ft.Text(label, size=11, color=color, font_family=FONT_MONO),
        padding=ft.padding.symmetric(horizontal=8, vertical=3),
        border=ft.border.all(1, color),
        border_radius=4,
    )


def section_title(text: str) -> ft.Text:
    return ft.Text(text, size=13, weight=ft.FontWeight.BOLD,
                   color=ACCENT2, font_family=FONT_MONO)


def card(content, padding=14) -> ft.Container:
    return ft.Container(
        content=content,
        bgcolor=CARD_BG,
        border=ft.border.all(1, BORDER),
        border_radius=8,
        padding=padding,
    )


def snack(page: ft.Page, msg: str, color: str = SUCCESS):
    page.snack_bar = ft.SnackBar(
        content=ft.Text(msg, color=TEXT),
        bgcolor=color,
        duration=3000,
    )
    page.snack_bar.open = True
    page.update()


# ─────────────────────────────────────────────
#  TABS
# ─────────────────────────────────────────────

class DefinicionTab:
    def __init__(self, page: ft.Page, afd: AFD, refresh_all):
        self.page = page
        self.afd = afd
        self.refresh_all = refresh_all
        self._build()

    def _build(self):
        self.tf_states    = ft.TextField(label="Estados (separados por coma)", hint_text="q0, q1, q2", bgcolor=CARD_BG, color=TEXT, label_style=ft.TextStyle(color=TEXT_MUTED), border_color=BORDER, focused_border_color=ACCENT, expand=True)
        self.tf_alphabet  = ft.TextField(label="Alfabeto (separados por coma)", hint_text="a, b", bgcolor=CARD_BG, color=TEXT, label_style=ft.TextStyle(color=TEXT_MUTED), border_color=BORDER, focused_border_color=ACCENT, expand=True)
        self.dd_initial   = ft.Dropdown(label="Estado inicial", bgcolor=CARD_BG, color=TEXT, label_style=ft.TextStyle(color=TEXT_MUTED), border_color=BORDER, focused_border_color=ACCENT, expand=True)
        self.cb_accept    = ft.Column(scroll=ft.ScrollMode.AUTO, height=80)
        self.table_area   = ft.Column()
        self.status_text  = ft.Text("", color=TEXT_MUTED, size=12, font_family=FONT_MONO)

        btn_gen = ft.ElevatedButton("1. Generar tabla", on_click=self._gen_table,
            style=ft.ButtonStyle(bgcolor=ACCENT, color=TEXT, shape=ft.RoundedRectangleBorder(radius=6)))
        btn_save = ft.ElevatedButton("2. Guardar AFD", on_click=self._save,
            style=ft.ButtonStyle(bgcolor=ACCENT2, color=TEXT, shape=ft.RoundedRectangleBorder(radius=6)))

        self.view = ft.Column([
            section_title("DEFINICIÓN MANUAL DEL AFD"),
            ft.Row([
                self.tf_states,
                self.tf_alphabet,
            ], spacing=10),
            ft.Row([
                self.dd_initial,
                ft.Container(
                    content=ft.Column([
                        ft.Text("Estados de aceptación:", color=TEXT_MUTED, size=12),
                        self.cb_accept,
                    ]),
                    expand=True,
                    bgcolor=CARD_BG, border=ft.border.all(1, BORDER), border_radius=6,
                    padding=8,
                ),
            ], spacing=10),
            ft.Row([btn_gen, btn_save], spacing=10),
            self.status_text,
            ft.Divider(color=BORDER),
            section_title("TABLA DE TRANSICIONES"),
            card(self.table_area),
        ], spacing=10, scroll=ft.ScrollMode.AUTO, expand=True)

    def _update_dropdowns(self):
        states_raw = [s.strip() for s in self.tf_states.value.split(",") if s.strip()]
        self.dd_initial.options = [ft.dropdown.Option(s) for s in states_raw]
        self.cb_accept.controls = [
            ft.Checkbox(label=s, value=s in self.afd.accept_states, fill_color=ACCENT2, check_color=TEXT)
            for s in states_raw
        ]
        self.page.update()

    def _gen_table(self, _):
        states_raw  = [s.strip() for s in self.tf_states.value.split(",") if s.strip()]
        alphabet_raw = [s.strip() for s in self.tf_alphabet.value.split(",") if s.strip()]
        if not states_raw or not alphabet_raw:
            snack(self.page, "Ingresa estados y alfabeto primero.", DANGER)
            return
        # Keep existing transitions
        old_trans = {s: dict(self.afd.transitions.get(s, {})) for s in self.afd.transitions}
        self.afd.clear()
        self.afd.alphabet = alphabet_raw
        for s in states_raw:
            self.afd.add_state(s)
            self.afd.transitions[s] = {sym: old_trans.get(s, {}).get(sym, "") for sym in alphabet_raw}
        self._update_dropdowns()
        self._render_table()
        self.status_text.value = f"Tabla generada: {len(states_raw)} estados × {len(alphabet_raw)} símbolos"
        self.page.update()

    def _render_table(self):
        self.table_area.controls.clear()
        if not self.afd.states or not self.afd.alphabet:
            return
        # Header row
        header_cells = [ft.DataColumn(ft.Text("Estado", color=ACCENT, size=12, font_family=FONT_MONO))]
        for sym in self.afd.alphabet:
            header_cells.append(ft.DataColumn(ft.Text(sym, color=ACCENT2, size=12, font_family=FONT_MONO)))

        # We'll store tf references to read on save
        self._trans_fields: dict[str, dict[str, ft.TextField]] = {}
        rows = []
        for st in self.afd.states:
            self._trans_fields[st] = {}
            cells = [ft.DataCell(ft.Text(st, color=TEXT, font_family=FONT_MONO, size=12))]
            for sym in self.afd.alphabet:
                existing = self.afd.transitions.get(st, {}).get(sym, "")
                tf = ft.TextField(
                    value=existing,
                    width=80,
                    height=36,
                    text_size=12,
                    bgcolor=DARK_BG,
                    color=TEXT,
                    border_color=BORDER,
                    focused_border_color=ACCENT,
                    content_padding=ft.padding.symmetric(horizontal=6, vertical=4),
                )
                self._trans_fields[st][sym] = tf
                cells.append(ft.DataCell(tf))
            rows.append(ft.DataRow(cells=cells))

        table = ft.DataTable(
            columns=header_cells,
            rows=rows,
            border=ft.border.all(1, BORDER),
            heading_row_color="#0d1929",
            data_row_color={"hovered": "#0d0a1a"},
            column_spacing=8,
        )
        self.table_area.controls.append(table)
        self.page.update()

    def _save(self, _):
        if not self.afd.states:
            snack(self.page, "Genera la tabla primero.", DANGER)
            return
        # Read initial state
        self.afd.initial_state = self.dd_initial.value
        # Read accept states
        self.afd.accept_states = [
            cb.label for cb in self.cb_accept.controls if isinstance(cb, ft.Checkbox) and cb.value
        ]
        # Read transitions from fields
        if hasattr(self, "_trans_fields"):
            for st, syms in self._trans_fields.items():
                for sym, tf in syms.items():
                    val = tf.value.strip()
                    if val:
                        self.afd.transitions[st][sym] = val
                    else:
                        self.afd.transitions[st].pop(sym, None)
        ok, msg = self.afd.is_valid_definition()
        if not ok:
            snack(self.page, f"AFD inválido: {msg}", DANGER)
            return
        snack(self.page, "✓ AFD guardado correctamente.")
        self.refresh_all()


class ImportacionTab:
    def __init__(self, page: ft.Page, afd: AFD, refresh_all):
        self.page = page
        self.afd = afd
        self.refresh_all = refresh_all
        self._build()

    def _build(self):
        self.info_area = ft.Column(scroll=ft.ScrollMode.AUTO, height=300)
        self.file_name = ft.Text("Ningún archivo seleccionado", color=TEXT_MUTED, size=12, font_family=FONT_MONO)

        btn_pick = ft.ElevatedButton(
            "📂  Cargar archivo (.jff / .json / .xml)",
            on_click=self._pick_file,
            style=ft.ButtonStyle(bgcolor=ACCENT, color=TEXT, shape=ft.RoundedRectangleBorder(radius=6))
        )

        self.view = ft.Column([
            section_title("IMPORTACIÓN DESDE ARCHIVO"),
            btn_pick,
            self.file_name,
            ft.Divider(color=BORDER),
            section_title("COMPONENTES DETECTADOS"),
            card(self.info_area),
        ], spacing=10, scroll=ft.ScrollMode.AUTO, expand=True)

    def _pick_file(self, _):
        import threading
        def open_dialog():
            import tkinter as tk
            from tkinter import filedialog
            root = tk.Tk()
            root.withdraw()
            root.attributes("-topmost", True)
            path = filedialog.askopenfilename(
                title="Seleccionar archivo AFD",
                filetypes=[
                    ("Archivos AFD", "*.jff *.json *.xml"),
                    ("JFLAP", "*.jff"),
                    ("JSON", "*.json"),
                    ("XML", "*.xml"),
                ]
            )
            root.destroy()
            if path:
                self._load_file(path)
        threading.Thread(target=open_dialog, daemon=True).start()

    def _load_file(self, path):
        import os
        name = os.path.basename(path)
        self.file_name.value = f"Archivo: {name}"
        try:
            with open(path, "r", encoding="utf-8") as fh:
                content = fh.read()
            ext = name.rsplit(".", 1)[-1].lower()
            if ext == "jff":
                loaded = AFD.from_jff(content)
            elif ext == "json":
                loaded = AFD.from_json(content)
            elif ext == "xml":
                loaded = AFD.from_xml(content)
            else:
                snack(self.page, "Formato no soportado.", DANGER)
                return
            self.afd.states        = loaded.states
            self.afd.alphabet      = loaded.alphabet
            self.afd.initial_state = loaded.initial_state
            self.afd.accept_states = loaded.accept_states
            self.afd.transitions   = loaded.transitions
            self._show_info()
            snack(self.page, f"✓ {name} cargado correctamente.")
            self.refresh_all()
        except Exception as ex:
            snack(self.page, f"Error al cargar: {ex}", DANGER)
        self.page.update()

    def _show_info(self):
        self.info_area.controls.clear()
        rows = [
            ("Alfabeto",         ", ".join(self.afd.alphabet) or "—"),
            ("Estados",          ", ".join(self.afd.states) or "—"),
            ("Estado inicial",   self.afd.initial_state or "—"),
            ("Estados aceptación", ", ".join(self.afd.accept_states) or "—"),
            ("Transiciones",     str(sum(len(v) for v in self.afd.transitions.values()))),
        ]
        for k, v in rows:
            self.info_area.controls.append(
                ft.Row([
                    ft.Text(f"{k}:", color=TEXT_MUTED, size=12, width=160, font_family=FONT_MONO),
                    ft.Text(v, color=TEXT, size=12, font_family=FONT_MONO),
                ])
            )
        self.page.update()


class SimulacionTab:
    def __init__(self, page: ft.Page, afd: AFD):
        self.page = page
        self.afd = afd
        self._trace: list = []
        self._step_idx = 0
        self._build()

    def _build(self):
        self.tf_string   = ft.TextField(label="Cadena a validar", hint_text="ej: aabb", bgcolor=CARD_BG, color=TEXT, label_style=ft.TextStyle(color=TEXT_MUTED), border_color=BORDER, focused_border_color=ACCENT, expand=True)
        self.result_text = ft.Text("", size=18, font_family=FONT_MONO, weight=ft.FontWeight.BOLD)
        self.trace_list  = ft.Column(scroll=ft.ScrollMode.AUTO, height=220)
        self.step_display = ft.Column(scroll=ft.ScrollMode.AUTO, height=100)
        self.step_counter = ft.Text("", color=TEXT_MUTED, size=12, font_family=FONT_MONO)
        self._current_accepted = False

        btn_validate = ft.ElevatedButton("▶  Validar",
            on_click=self._validate,
            style=ft.ButtonStyle(bgcolor=ACCENT, color=TEXT, shape=ft.RoundedRectangleBorder(radius=6)))
        btn_step_back = ft.IconButton("skip_previous", on_click=self._step_back, icon_color=ACCENT2)
        btn_step_fwd  = ft.IconButton("skip_next", on_click=self._step_fwd, icon_color=ACCENT2)
        btn_reset_step = ft.IconButton("replay", on_click=self._reset_step, icon_color=TEXT_MUTED)

        self.view = ft.Column([
            section_title("SIMULACIÓN Y VALIDACIÓN DE CADENAS"),
            ft.Row([self.tf_string, btn_validate], spacing=10),
            card(ft.Column([
                ft.Text("Resultado:", color=TEXT_MUTED, size=12),
                self.result_text,
            ])),
            ft.Divider(color=BORDER),
            section_title("TRAZA COMPLETA"),
            card(self.trace_list),
            ft.Divider(color=BORDER),
            section_title("SIMULACIÓN PASO A PASO"),
            ft.Row([btn_reset_step, btn_step_back, self.step_counter, btn_step_fwd], spacing=6),
            card(self.step_display),
        ], spacing=10, scroll=ft.ScrollMode.AUTO, expand=True)

    def _validate(self, _):
        ok, msg = self.afd.is_valid_definition()
        if not ok:
            snack(self.page, f"AFD no definido: {msg}", DANGER)
            return
        s = self.tf_string.value
        accepted, trace = self.afd.validate(s)
        self._current_accepted = accepted
        self._trace = trace
        self._step_idx = 0

        self.result_text.value = ("✓  ACEPTADA" if accepted else "✗  RECHAZADA")
        self.result_text.color = SUCCESS if accepted else DANGER

        self.trace_list.controls.clear()
        if not trace:
            self.trace_list.controls.append(
                ft.Text("(cadena vacía — estado inicial directo)", color=TEXT_MUTED, size=12, font_family=FONT_MONO)
            )
        for i, (frm, sym, to) in enumerate(trace):
            color = DANGER if to == "DEAD" else TEXT
            self.trace_list.controls.append(
                ft.Text(f"  {i+1:2}. δ({frm}, '{sym}') = {to}", color=color, size=12, font_family=FONT_MONO)
            )
        self._render_step()
        self.page.update()

    def _render_step(self):
        self.step_display.controls.clear()
        if not self._trace:
            self.step_counter.value = "Paso 0 / 0"
            initial = self.afd.initial_state or "—"
            label = f"Estado inicial: {initial}"
            self.step_display.controls.append(
                ft.Text(label, color=TEXT, font_family=FONT_MONO, size=13)
            )
            self.page.update()
            return

        self.step_counter.value = f"Paso {self._step_idx} / {len(self._trace)}"
        consumed = self.tf_string.value[:self._step_idx]
        remaining = self.tf_string.value[self._step_idx:]

        if self._step_idx == 0:
            cur_state = self.afd.initial_state or "—"
        else:
            cur_state = self._trace[self._step_idx - 1][2]

        color = SUCCESS if cur_state in self.afd.accept_states else (DANGER if cur_state == "DEAD" else ACCENT)
        self.step_display.controls += [
            ft.Row([
                ft.Text("Estado actual:", color=TEXT_MUTED, size=12, width=130, font_family=FONT_MONO),
                ft.Container(
                    content=ft.Text(cur_state, color=color, size=13, font_family=FONT_MONO, weight=ft.FontWeight.BOLD),
                    border=ft.border.all(2, color), border_radius=6, padding=ft.padding.symmetric(4, 8)
                ),
            ]),
            ft.Row([
                ft.Text("Consumido:", color=TEXT_MUTED, size=12, width=130, font_family=FONT_MONO),
                ft.Text(f'"{consumed}"', color=ACCENT2, size=12, font_family=FONT_MONO),
                ft.Text("Restante:", color=TEXT_MUTED, size=12, width=80, font_family=FONT_MONO),
                ft.Text(f'"{remaining}"', color=TEXT, size=12, font_family=FONT_MONO),
            ]),
        ]
        if self._step_idx < len(self._trace):
            frm, sym, to = self._trace[self._step_idx]
            self.step_display.controls.append(
                ft.Text(f"  → δ({frm}, '{sym}') = {to}", color=ACCENT, size=12, font_family=FONT_MONO)
            )
        self.page.update()

    def _step_fwd(self, _):
        if self._step_idx < len(self._trace):
            self._step_idx += 1
            self._render_step()

    def _step_back(self, _):
        if self._step_idx > 0:
            self._step_idx -= 1
            self._render_step()

    def _reset_step(self, _):
        self._step_idx = 0
        self._render_step()


class ExportacionTab:
    def __init__(self, page: ft.Page, afd: AFD):
        self.page = page
        self.afd = afd
        self._build()

    def _build(self):
        self.preview_area = ft.TextField(
            multiline=True, min_lines=16, max_lines=24,
            bgcolor=DARK_BG, color=TEXT, border_color=BORDER,
            text_style=ft.TextStyle(font_family=FONT_MONO, size=11),
            read_only=True,
        )
        self._current_content = ""
        self._current_ext = "jff"

        def make_btn(label, ext, color):
            return ft.ElevatedButton(
                label,
                on_click=lambda _, e=ext: self._preview(e),
                style=ft.ButtonStyle(bgcolor=color, color=TEXT, shape=ft.RoundedRectangleBorder(radius=6))
            )

        btn_jff  = make_btn("Ver / Guardar .jff",  "jff",  ACCENT)
        btn_json = make_btn("Ver / Guardar .json", "json", ACCENT2)
        btn_xml  = make_btn("Ver / Guardar .xml",  "xml",  "#10b981")

        btn_save = ft.ElevatedButton(
            "💾  Guardar archivo",
            on_click=self._save_file,
            style=ft.ButtonStyle(bgcolor="#f59e0b", color=DARK_BG, shape=ft.RoundedRectangleBorder(radius=6))
        )

        self.view = ft.Column([
            section_title("EXPORTACIÓN DE AFD"),
            ft.Row([btn_jff, btn_json, btn_xml, btn_save], spacing=10, wrap=True),
            ft.Divider(color=BORDER),
            section_title("VISTA PREVIA"),
            self.preview_area,
        ], spacing=10, scroll=ft.ScrollMode.AUTO, expand=True)

    def _preview(self, ext: str):
        ok, msg = self.afd.is_valid_definition()
        if not ok:
            snack(self.page, f"AFD no definido: {msg}", DANGER)
            return
        self._current_ext = ext
        if ext == "jff":
            self._current_content = self.afd.to_jff()
        elif ext == "json":
            self._current_content = self.afd.to_json()
        else:
            self._current_content = self.afd.to_xml()
        self.preview_area.value = self._current_content
        self.page.update()

    def _save_file(self, _):
        if not self._current_content:
            snack(self.page, "Genera una vista previa primero.", DANGER)
            return
        import threading
        ext = self._current_ext
        content_to_save = self._current_content
        def open_dialog():
            import tkinter as tk
            from tkinter import filedialog
            root = tk.Tk()
            root.withdraw()
            root.attributes("-topmost", True)
            path = filedialog.asksaveasfilename(
                defaultextension=f".{ext}",
                initialfile=f"automata.{ext}",
                filetypes=[(ext.upper(), f"*.{ext}")]
            )
            root.destroy()
            if path:
                try:
                    with open(path, "w", encoding="utf-8") as fh:
                        fh.write(content_to_save)
                    snack(self.page, f"✓ Guardado en {path}")
                except Exception as ex:
                    snack(self.page, f"Error: {ex}", DANGER)
        threading.Thread(target=open_dialog, daemon=True).start()


class SubcadenasTab:
    def __init__(self, page: ft.Page):
        self.page = page
        self._build()

    def _build(self):
        self.tf_input = ft.TextField(
            label="Cadena de entrada",
            hint_text="ej: abc",
            bgcolor=CARD_BG, color=TEXT,
            label_style=ft.TextStyle(color=TEXT_MUTED),
            border_color=BORDER, focused_border_color=ACCENT,
            expand=True,
        )
        self.pref_col  = ft.Column(scroll=ft.ScrollMode.AUTO, height=160)
        self.suf_col   = ft.Column(scroll=ft.ScrollMode.AUTO, height=160)
        self.sub_col   = ft.Column(scroll=ft.ScrollMode.AUTO, height=160)
        self._last_results = ""

        btn_calc = ft.ElevatedButton(
            "Calcular",
            on_click=self._calc,
            style=ft.ButtonStyle(bgcolor=ACCENT, color=TEXT, shape=ft.RoundedRectangleBorder(radius=6))
        )
        btn_save = ft.ElevatedButton(
            "💾  Exportar .txt",
            on_click=self._save_txt,
            style=ft.ButtonStyle(bgcolor="#f59e0b", color=DARK_BG, shape=ft.RoundedRectangleBorder(radius=6))
        )

        self.view = ft.Column([
            section_title("SUBCADENAS, PREFIJOS Y SUFIJOS"),
            ft.Row([self.tf_input, btn_calc, btn_save], spacing=10),
            ft.Row([
                ft.Column([section_title("PREFIJOS"), card(self.pref_col)], expand=True),
                ft.Column([section_title("SUFIJOS"),  card(self.suf_col)], expand=True),
                ft.Column([section_title("SUBCADENAS"), card(self.sub_col)], expand=True),
            ], spacing=10),
        ], spacing=10, scroll=ft.ScrollMode.AUTO, expand=True)

    def _make_chips(self, items: list[str]) -> list[ft.Control]:
        return [ft.Text(f'"{x}"' if x else '""', color=TEXT, size=11, font_family=FONT_MONO) for x in items]

    def _calc(self, _):
        s = self.tf_input.value
        prefs = get_prefixes(s)
        suffs = get_suffixes(s)
        subs  = get_substrings(s)

        self.pref_col.controls = self._make_chips(prefs)
        self.suf_col.controls  = self._make_chips(suffs)
        self.sub_col.controls  = self._make_chips(subs)

        self._last_results = (
            f"Cadena: {s}\n\n"
            f"Prefijos ({len(prefs)}):\n" + "\n".join(f'  "{p}"' for p in prefs) + "\n\n"
            f"Sufijos ({len(suffs)}):\n"  + "\n".join(f'  "{s2}"' for s2 in suffs) + "\n\n"
            f"Subcadenas ({len(subs)}):\n" + "\n".join(f'  "{sb}"' for sb in subs)
        )
        self.page.update()

    def _save_txt(self, _):
        if not self._last_results:
            snack(self.page, "Calcula primero las subcadenas.", DANGER)
            return
        import threading
        data = self._last_results
        def open_dialog():
            import tkinter as tk
            from tkinter import filedialog
            root = tk.Tk()
            root.withdraw()
            root.attributes("-topmost", True)
            path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                initialfile="subcadenas.txt",
                filetypes=[("Texto", "*.txt")]
            )
            root.destroy()
            if path:
                try:
                    with open(path, "w", encoding="utf-8") as fh:
                        fh.write(data)
                    snack(self.page, f"✓ Guardado en {path}")
                except Exception as ex:
                    snack(self.page, f"Error: {ex}", DANGER)
        threading.Thread(target=open_dialog, daemon=True).start()


class KleeneTab:
    def __init__(self, page: ft.Page, afd: AFD):
        self.page = page
        self.afd = afd
        self._build()

    def _build(self):
        self.tf_alphabet = ft.TextField(
            label="Alfabeto (separados por coma, o usa el del AFD)",
            hint_text="a, b",
            bgcolor=CARD_BG, color=TEXT,
            label_style=ft.TextStyle(color=TEXT_MUTED),
            border_color=BORDER, focused_border_color=ACCENT,
            expand=True,
        )
        self.tf_maxlen = ft.TextField(
            label="Longitud máxima",
            value="3",
            width=140,
            bgcolor=CARD_BG, color=TEXT,
            label_style=ft.TextStyle(color=TEXT_MUTED),
            border_color=BORDER, focused_border_color=ACCENT,
        )
        self.star_col = ft.Column(scroll=ft.ScrollMode.AUTO, height=200)
        self.plus_col = ft.Column(scroll=ft.ScrollMode.AUTO, height=200)
        self.count_star = ft.Text("", color=TEXT_MUTED, size=12, font_family=FONT_MONO)
        self.count_plus = ft.Text("", color=TEXT_MUTED, size=12, font_family=FONT_MONO)
        self._last_results = ""

        btn_use_afd = ft.TextButton(
            "Usar alfabeto del AFD",
            on_click=self._use_afd_alphabet,
            style=ft.ButtonStyle(color=ACCENT2),
        )
        btn_calc = ft.ElevatedButton(
            "Calcular",
            on_click=self._calc,
            style=ft.ButtonStyle(bgcolor=ACCENT, color=TEXT, shape=ft.RoundedRectangleBorder(radius=6))
        )
        btn_save = ft.ElevatedButton(
            "💾  Exportar .txt",
            on_click=self._save_txt,
            style=ft.ButtonStyle(bgcolor="#f59e0b", color=DARK_BG, shape=ft.RoundedRectangleBorder(radius=6))
        )

        self.view = ft.Column([
            section_title("CERRADURA DE KLEENE (Σ*) Y POSITIVA (Σ+)"),
            ft.Row([self.tf_alphabet, self.tf_maxlen], spacing=10),
            ft.Row([btn_use_afd, btn_calc, btn_save], spacing=10),
            ft.Row([
                ft.Column([section_title("Σ* (Kleene Star)"), self.count_star, card(self.star_col)], expand=True),
                ft.Column([section_title("Σ+ (Kleene Plus)"), self.count_plus, card(self.plus_col)], expand=True),
            ], spacing=10),
        ], spacing=10, scroll=ft.ScrollMode.AUTO, expand=True)

    def _use_afd_alphabet(self, _):
        if self.afd.alphabet:
            self.tf_alphabet.value = ", ".join(self.afd.alphabet)
            self.page.update()
        else:
            snack(self.page, "El AFD no tiene alfabeto definido.", DANGER)

    def _calc(self, _):
        alph = [s.strip() for s in self.tf_alphabet.value.split(",") if s.strip()]
        if not alph:
            snack(self.page, "Ingresa un alfabeto.", DANGER)
            return
        try:
            maxlen = int(self.tf_maxlen.value)
            if maxlen < 1 or maxlen > 6:
                raise ValueError
        except ValueError:
            snack(self.page, "Longitud máxima debe ser entre 1 y 6.", DANGER)
            return

        star = kleene_star(alph, maxlen)
        plus = kleene_plus(alph, maxlen)

        self.count_star.value = f"Total: {len(star)} cadenas"
        self.count_plus.value = f"Total: {len(plus)} cadenas"

        self.star_col.controls = [
            ft.Text(f'"{w}"' if w else '""', color=TEXT, size=11, font_family=FONT_MONO)
            for w in star[:500]
        ]
        if len(star) > 500:
            self.star_col.controls.append(ft.Text("... (truncado a 500)", color=TEXT_MUTED, size=11))

        self.plus_col.controls = [
            ft.Text(f'"{w}"', color=TEXT, size=11, font_family=FONT_MONO)
            for w in plus[:500]
        ]
        if len(plus) > 500:
            self.plus_col.controls.append(ft.Text("... (truncado a 500)", color=TEXT_MUTED, size=11))

        self._last_results = (
            f"Alfabeto: {{{', '.join(alph)}}}\n"
            f"Longitud máxima: {maxlen}\n\n"
            f"Σ* (Kleene Star) — {len(star)} cadenas:\n" + "\n".join(f'  "{w}"' for w in star) + "\n\n"
            f"Σ+ (Kleene Plus) — {len(plus)} cadenas:\n" + "\n".join(f'  "{w}"' for w in plus)
        )
        self.page.update()

    def _save_txt(self, _):
        if not self._last_results:
            snack(self.page, "Calcula primero el Kleene.", DANGER)
            return
        import threading
        data = self._last_results
        def open_dialog():
            import tkinter as tk
            from tkinter import filedialog
            root = tk.Tk()
            root.withdraw()
            root.attributes("-topmost", True)
            path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                initialfile="kleene.txt",
                filetypes=[("Texto", "*.txt")]
            )
            root.destroy()
            if path:
                try:
                    with open(path, "w", encoding="utf-8") as fh:
                        fh.write(data)
                    snack(self.page, f"✓ Guardado en {path}")
                except Exception as ex:
                    snack(self.page, f"Error: {ex}", DANGER)
        threading.Thread(target=open_dialog, daemon=True).start()


# ─────────────────────────────────────────────
#  VISUAL TAB (diagrama de estados simplificado)
# ─────────────────────────────────────────────

class VisualizacionTab:
    def __init__(self, page: ft.Page, afd: AFD):
        self.page = page
        self.afd = afd
        self.canvas_area = ft.Column(scroll=ft.ScrollMode.AUTO)
        self.view = ft.Column([
            section_title("VISUALIZACIÓN DEL AFD"),
            ft.Text("(Representación tabular + resumen — para diagramas completos exporta a JFLAP)", color=TEXT_MUTED, size=11),
            ft.Divider(color=BORDER),
            self.canvas_area,
        ], spacing=10, scroll=ft.ScrollMode.AUTO, expand=True)

    def refresh(self):
        self.canvas_area.controls.clear()
        afd = self.afd
        if not afd.states:
            self.canvas_area.controls.append(ft.Text("No hay AFD definido.", color=TEXT_MUTED, font_family=FONT_MONO))
            self.page.update()
            return

        # Summary chips
        chips_row = ft.Row(wrap=True, spacing=6)
        for s in afd.states:
            color = ACCENT
            label = s
            if s == afd.initial_state and s in afd.accept_states:
                color = "#f59e0b"; label = f"→ {s} ✓"
            elif s == afd.initial_state:
                color = ACCENT2; label = f"→ {s}"
            elif s in afd.accept_states:
                color = SUCCESS; label = f"{s} ✓"
            chips_row.controls.append(make_chip(label, color))

        # Transition table
        header = [ft.DataColumn(ft.Text("δ", color=ACCENT, size=12, font_family=FONT_MONO))]
        for sym in afd.alphabet:
            header.append(ft.DataColumn(ft.Text(sym, color=ACCENT2, size=12, font_family=FONT_MONO)))
        rows = []
        for st in afd.states:
            label = st
            if st == afd.initial_state:
                label = "→ " + label
            if st in afd.accept_states:
                label = label + " ✓"
            cells = [ft.DataCell(ft.Text(label, color=TEXT, font_family=FONT_MONO, size=12))]
            for sym in afd.alphabet:
                val = afd.transitions.get(st, {}).get(sym, "—")
                cells.append(ft.DataCell(ft.Text(val, color=TEXT if val != "—" else TEXT_MUTED, font_family=FONT_MONO, size=12)))
            rows.append(ft.DataRow(cells=cells))

        table = ft.DataTable(
            columns=header, rows=rows,
            border=ft.border.all(1, BORDER),
            heading_row_color="#0d1929",
            column_spacing=12,
        )

        self.canvas_area.controls += [
            ft.Text("Estados:", color=TEXT_MUTED, size=12),
            chips_row,
            ft.Row([
                make_chip(f"Alfabeto: {{{', '.join(afd.alphabet)}}}", ACCENT),
                make_chip(f"Inicial: {afd.initial_state or '—'}", ACCENT2),
                make_chip(f"Aceptación: {{{', '.join(afd.accept_states)}}}", SUCCESS),
            ], wrap=True, spacing=6),
            ft.Divider(color=BORDER),
            ft.Text("Tabla de transiciones:", color=TEXT_MUTED, size=12),
            table,
        ]
        self.page.update()


# ─────────────────────────────────────────────
#  MAIN APP
# ─────────────────────────────────────────────

def main(page: ft.Page):
    page.title = "AFD Simulator"
    page.bgcolor = DARK_BG
    page.theme_mode = ft.ThemeMode.DARK
    page.padding = 0
    page.fonts = {}

    afd = AFD()

    # Tabs
    vis_tab   = VisualizacionTab(page, afd)
    def_tab   = DefinicionTab(page, afd, lambda: vis_tab.refresh())
    imp_tab   = ImportacionTab(page, afd, lambda: vis_tab.refresh())
    sim_tab   = SimulacionTab(page, afd)
    exp_tab   = ExportacionTab(page, afd)
    sub_tab   = SubcadenasTab(page)
    kle_tab   = KleeneTab(page, afd)

    # ─── Header ────────────────────────────────
    header = ft.Container(
        content=ft.Row([
            ft.Column([
                ft.Text("AFD SIMULATOR", size=20, weight=ft.FontWeight.BOLD, color=ACCENT, font_family=FONT_MONO),
                ft.Text("Autómatas Finitos Deterministas", size=11, color=TEXT_MUTED, font_family=FONT_MONO),
            ]),
            ft.Row([
                make_chip("Python + Flet", ACCENT2),
                make_chip(".jff / .json / .xml", ACCENT),
            ], spacing=8),
        ], alignment=ft.MainAxisAlignment.SPACE_BETWEEN),
        bgcolor=PANEL_BG,
        border=ft.border.only(bottom=ft.BorderSide(1, BORDER)),
        padding=ft.padding.symmetric(horizontal=20, vertical=12),
    )

    # ─── Tab bar ───────────────────────────────
    TAB_LABELS = [
        ("⊞  Definición",   def_tab.view),
        ("⤓  Importar",     imp_tab.view),
        ("▶  Simulación",   sim_tab.view),
        ("◈  Visual",       vis_tab.view),
        ("↑  Exportar",     exp_tab.view),
        ("⊂  Subcadenas",   sub_tab.view),
        ("∗  Kleene",       kle_tab.view),
    ]

    content_area = ft.Container(expand=True, padding=20)
    active_idx = [0]
    tab_buttons: list[ft.TextButton] = []

    def switch_tab(idx: int):
        active_idx[0] = idx
        content_area.content = TAB_LABELS[idx][1]
        if idx == 3:
            vis_tab.refresh()
        for i, btn in enumerate(tab_buttons):
            btn.style = ft.ButtonStyle(
                color=ACCENT if i == idx else TEXT_MUTED,
                bgcolor="#0d1929" if i == idx else "transparent",
                shape=ft.RoundedRectangleBorder(radius=0),
                padding=ft.padding.symmetric(horizontal=14, vertical=10),
            )
        page.update()

    for i, (label, _) in enumerate(TAB_LABELS):
        idx = i
        btn = ft.TextButton(
            label,
            on_click=lambda _, i=idx: switch_tab(i),
            style=ft.ButtonStyle(
                color=TEXT_MUTED,
                bgcolor="transparent",
                shape=ft.RoundedRectangleBorder(radius=0),
                padding=ft.padding.symmetric(horizontal=14, vertical=10),
            ),
        )
        tab_buttons.append(btn)

    tab_bar = ft.Container(
        content=ft.Row(tab_buttons, spacing=0),
        bgcolor=PANEL_BG,
        border=ft.border.only(bottom=ft.BorderSide(1, BORDER)),
    )

    switch_tab(0)

    page.add(
        ft.Column([
            header,
            tab_bar,
            content_area,
        ], spacing=0, expand=True)
    )


ft.app(target=main)
