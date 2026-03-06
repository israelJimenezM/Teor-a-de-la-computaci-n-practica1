import tkinter as tk
from tkinter import ttk

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


# ---------------- GUI ----------------

def mostrar_lista(widget, lista):

    widget.delete("1.0", tk.END)

    i = 0
    while i < len(lista):

        widget.insert(tk.END, lista[i] + "\n")
        i = i + 1


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

    alfabeto = entradaAlfabeto.get()
    n = int(entradaN.get())

    lista = []

    i = 0
    while i < len(alfabeto):

        lista.append(alfabeto[i])
        i = i + 1

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
entradaCadena.insert(0,"")   # ejemplo

incluirVacia = tk.BooleanVar()

ttk.Checkbutton(frame1,text="Incluir λ",variable=incluirVacia).grid(row=0,column=2)

ttk.Button(frame1,text="Calcular",command=calcular).grid(row=0,column=3,padx=5)

resFrame = ttk.Frame(tab1)
resFrame.pack(fill="both",expand=True,padx=10)

ttk.Label(resFrame,text="Prefijos").grid(row=0,column=0)
txtPref = tk.Text(resFrame,height=20,width=25)
txtPref.grid(row=1,column=0)

ttk.Label(resFrame,text="Subcadenas").grid(row=0,column=1)
txtSub = tk.Text(resFrame,height=20,width=40)
txtSub.grid(row=1,column=1)

ttk.Label(resFrame,text="Sufijos").grid(row=0,column=2)
txtSuf = tk.Text(resFrame,height=20,width=25)
txtSuf.grid(row=1,column=2)


# ---------- TAB 2 ----------

tab2 = ttk.Frame(tabs)
tabs.add(tab2,text="Cerraduras (Σ*, Σ+)")

frame2 = ttk.Frame(tab2)
frame2.pack(pady=10)

ttk.Label(frame2,text="Alfabeto (ejemplo: abcd)").grid(row=0,column=0)

entradaAlfabeto = ttk.Entry(frame2,width=20)
entradaAlfabeto.grid(row=0,column=1)
entradaAlfabeto.insert(0,"")   # ejemplo

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

ttk.Label(res2,text="Σ+ (Positiva)").grid(row=0,column=1)
txtPlus = tk.Text(res2,height=20,width=40)
txtPlus.grid(row=1,column=1)


# ---------- TAB 3 ----------

tab3 = ttk.Frame(tabs)
tabs.add(tab3,text="Ayuda")

texto = """
Instrucciones:

- En la pestaña 'Sub/Pref/Suf' introduce una cadena (ejemplo: abbab)
  y presiona 'Calcular'.

Prefijos: comienzan desde el inicio de la cadena.
Sufijos: terminan al final de la cadena.
Subcadenas: partes continuas de la cadena.

- Puedes incluir la cadena vacía (λ).

- En la pestaña 'Cerraduras (Σ*, Σ+)' introduce un alfabeto
  (ejemplo: abcd) y la longitud máxima n.

Σ* contiene todas las cadenas posibles incluyendo λ.
Σ+ contiene todas las cadenas excepto λ.
"""

txtHelp = tk.Text(tab3)
txtHelp.insert("1.0",texto)
txtHelp.config(state="disabled")
txtHelp.pack(fill="both",expand=True,padx=20,pady=20)

ventana.mainloop()