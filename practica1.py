import tkinter as tk
from tkinter import ttk, filedialog, messagebox

# ---------------- FUNCIONES ----------------

def prefijos(cadena, vacia):

    res = []

    if vacia:
        res.append("λ")

    i = 1
    while i <= len(cadena):

        res.append(cadena[0:i])
        i = i + 1

    return res


def sufijos(cadena, vacia):

    res = []

    if vacia:
        res.append("λ")

    i = 1
    while i <= len(cadena):

        res.append(cadena[len(cadena)-i:])
        i = i + 1

    return res


def subcadenas(cadena, vacia):

    res = []

    if vacia:
        res.append("λ")

    i = 0
    while i < len(cadena):

        j = i + 1
        while j <= len(cadena):

            sub = cadena[i:j]

            if sub not in res:
                res.append(sub)

            j = j + 1

        i = i + 1

    return res


# ----------- INTERPRETAR ALFABETO -----------

def parse_alfabeto(texto):

    texto = texto.strip()

    if "," in texto:
        partes = texto.split(",")
        return [p.strip() for p in partes if p.strip() != ""]

    if " " in texto:
        partes = texto.split()
        return [p.strip() for p in partes if p.strip() != ""]

    return list(texto)


# ----------- CERRADURAS -----------

def generar(alfabeto, n, incluir_vacia):

    res = []

    if incluir_vacia:
        res.append("λ")

    cola = []

    i = 0
    while i < len(alfabeto):
        cola.append(alfabeto[i])
        i = i + 1

    while len(cola) > 0:

        actual = cola.pop(0)

        if len(actual) <= n:
            res.append(actual)

        if len(actual) < n:

            i = 0
            while i < len(alfabeto):

                cola.append(actual + alfabeto[i])
                i = i + 1

    return res


# ---------------- FUNCIONES GUI ----------------

def mostrar_lista(widget, lista):

    widget.delete("1.0", tk.END)

    i = 0
    while i < len(lista):

        widget.insert(tk.END, lista[i] + "\n")
        i = i + 1


def guardar_texto(widget, nombre):

    contenido = widget.get("1.0", tk.END).strip()

    if contenido == "":
        messagebox.showinfo("Vacío","No hay datos para guardar")
        return

    archivo = filedialog.asksaveasfilename(
        defaultextension=".txt",
        initialfile=nombre + ".txt",
        filetypes=[("Archivos de texto","*.txt")]
    )

    if archivo:

        f = open(archivo,"w",encoding="utf-8")
        f.write(contenido)
        f.close()

        messagebox.showinfo("Guardado","Archivo guardado correctamente")


# ---------------- CALCULOS ----------------

def calcular():

    cadena = entradaCadena.get()
    vacia = incluirVacia.get()

    p = prefijos(cadena, vacia)
    s = sufijos(cadena, vacia)
    sub = subcadenas(cadena, vacia)

    mostrar_lista(txtPref, p)
    mostrar_lista(txtSuf, s)
    mostrar_lista(txtSub, sub)


def calcular_kleene():

    texto = entradaAlfabeto.get()
    n = int(entradaN.get())

    lista = parse_alfabeto(texto)

    estrella = generar(lista, n, True)
    positiva = generar(lista, n, False)

    mostrar_lista(txtStar, estrella)
    mostrar_lista(txtPlus, positiva)


# ---------------- INTERFAZ ----------------

ventana = tk.Tk()
ventana.title("Operaciones con Cadenas")
ventana.geometry("900x600")

tabs = ttk.Notebook(ventana)
tabs.pack(fill="both", expand=True)

# ---------- TAB 1 ----------

tab1 = ttk.Frame(tabs)
tabs.add(tab1, text="Sub/Pref/Suf")

frame1 = ttk.Frame(tab1)
frame1.pack(pady=10)

ttk.Label(frame1,text="Cadena (ejemplo: abbab)").grid(row=0,column=0)

entradaCadena = ttk.Entry(frame1,width=30)
entradaCadena.grid(row=0,column=1)

incluirVacia = tk.BooleanVar()

ttk.Checkbutton(frame1,text="Incluir λ",variable=incluirVacia).grid(row=0,column=2)

ttk.Button(frame1,text="Calcular",command=calcular).grid(row=0,column=3,padx=5)

resFrame = ttk.Frame(tab1)
resFrame.pack(fill="both",expand=True,padx=10)

ttk.Label(resFrame,text="Prefijos").grid(row=0,column=0)
txtPref = tk.Text(resFrame,height=20,width=25)
txtPref.grid(row=1,column=0)

ttk.Button(resFrame,text="Guardar Prefijos",
command=lambda: guardar_texto(txtPref,"prefijos")).grid(row=2,column=0)

ttk.Label(resFrame,text="Subcadenas").grid(row=0,column=1)
txtSub = tk.Text(resFrame,height=20,width=40)
txtSub.grid(row=1,column=1)

ttk.Button(resFrame,text="Guardar Subcadenas",
command=lambda: guardar_texto(txtSub,"subcadenas")).grid(row=2,column=1)

ttk.Label(resFrame,text="Sufijos").grid(row=0,column=2)
txtSuf = tk.Text(resFrame,height=20,width=25)
txtSuf.grid(row=1,column=2)

ttk.Button(resFrame,text="Guardar Sufijos",
command=lambda: guardar_texto(txtSuf,"sufijos")).grid(row=2,column=2)


# ---------- TAB 2 ----------

tab2 = ttk.Frame(tabs)
tabs.add(tab2,text="Cerraduras (Σ*, Σ+)")

frame2 = ttk.Frame(tab2)
frame2.pack(pady=10)

ttk.Label(frame2,text="Alfabeto (ej: abc  o  a,b,c)").grid(row=0,column=0)

entradaAlfabeto = ttk.Entry(frame2,width=20)
entradaAlfabeto.grid(row=0,column=1)

ttk.Label(frame2,text="Longitud máxima").grid(row=1,column=0)

entradaN = ttk.Entry(frame2,width=5)
entradaN.insert(0,"3")
entradaN.grid(row=1,column=1)

ttk.Button(frame2,text="Generar",command=calcular_kleene).grid(row=0,column=2,rowspan=2,padx=5)

res2 = ttk.Frame(tab2)
res2.pack(fill="both",expand=True,padx=10)

ttk.Label(res2,text="Σ* (Kleene)").grid(row=0,column=0)
txtStar = tk.Text(res2,height=20,width=40)
txtStar.grid(row=1,column=0)

ttk.Button(res2,text="Guardar Σ*",
command=lambda: guardar_texto(txtStar,"sigma_star")).grid(row=2,column=0)

ttk.Label(res2,text="Σ+ (Positiva)").grid(row=0,column=1)
txtPlus = tk.Text(res2,height=20,width=40)
txtPlus.grid(row=1,column=1)

ttk.Button(res2,text="Guardar Σ+",
command=lambda: guardar_texto(txtPlus,"sigma_plus")).grid(row=2,column=1)


# ---------- TAB 3 (AYUDA) ----------

tab3 = ttk.Frame(tabs)
tabs.add(tab3,text="Ayuda")

texto = """
INSTRUCCIONES

1. Pestaña 'Sub/Pref/Suf'
Introduce una cadena (ejemplo: abbab) y presiona 'Calcular'.

Prefijos:
Son las cadenas que comienzan desde el inicio.
Ejemplo para 'abc':
a
ab
abc

Sufijos:
Son las cadenas que terminan al final.
Ejemplo:
c
bc
abc

Subcadenas:
Son todas las partes continuas dentro de la cadena.

Puedes incluir la cadena vacía λ activando la casilla.

-------------------------------------

2. Pestaña 'Cerraduras (Σ*, Σ+)'

Introduce un alfabeto y una longitud máxima.

Puedes escribir el alfabeto de tres formas:

abc
a,b,c
a b c

Σ* (Cerradura de Kleene)
Contiene todas las cadenas posibles incluyendo λ.

Σ+ (Cerradura positiva)
Contiene todas las cadenas posibles excepto λ.

-------------------------------------

3. Guardar resultados

Cada sección tiene un botón 'Guardar'.
Esto exporta los resultados a un archivo .txt.
"""

txtHelp = tk.Text(tab3)
txtHelp.insert("1.0",texto)
txtHelp.config(state="disabled")
txtHelp.pack(fill="both",expand=True,padx=20,pady=20)


ventana.mainloop()
