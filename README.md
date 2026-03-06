# Aplicacion de Operaciones sobre Lenguajes Formales

Esta practica es una herramienta con interfaz grafica (GUI) desarrollada en Python para procesar cadenas con tkinter y generar lenguajes basados en alfabetos. Permite realizar analisis de estructuras de cadenas y calculos de cerraduras de Kleene y Positivas.

---

## Requerimientos del Sistema

Para ejecutar este programa, asegurese de cumplir con lo siguiente:

* **Lenguaje:** Python 3.14.3,version 3.6 o superior recomendada.
* **Librerias:** * tkinter: Viene preinstalada con Python en Windows y macOS. 
    * Nota para usuarios de Linux (Ubuntu/Debian): Si no la tiene, instalela con `sudo apt-get install python3-tk`.
* **Hardware:** No requiere hardware especial, pero tenga en cuenta que la generacion masiva de cadenas consume memoria RAM.

---

## Guia de Uso por Pestañas

La aplicacion organiza sus funciones en tres secciones principales:

### 1. Pestaña: Sub/Pref/Suf
En esta seccion puede analizar la estructura interna de una cadena.
* **Entrada:** Escriba una palabra (ej. hola) y decida si incluir la cadena vacia ($\lambda$).
* **Resultados:** Se muestran tres columnas independientes:
    * **Prefijos:** Todas las cadenas iniciales posibles.
    * **Sufijos:** Todas las cadenas finales posibles.
    * **Subcadenas:** Todas las combinaciones contiguas unicas, ordenadas por aparicion.
* **Accion:** Botones individuales para Guardar cada lista en un archivo .txt.

### 2. Pestaña: Cerraduras (Σ*, Σ+)
Seccion dedicada a la generacion de lenguajes formales.
* **Entrada:** Introduce un alfabeto (ej: 0,1 o abc) y la longitud maxima $n$.
* **Resultados:** * **Σ* (Kleene):** Genera el conjunto de todas las cadenas de longitud 0 hasta $n$.
    * **Σ+ (Positiva):** Genera el conjunto de todas las cadenas de longitud 1 hasta $n$.
* **Seguridad:** El programa muestra un aviso si la generacion excede las 20,000 cadenas para proteger la estabilidad de su sistema.

### 3. Pestaña: Ayuda / Info
Contiene un resumen rapido de las reglas matematicas y los limites de generacion para consulta rapida del usuario.

---

## Instrucciones de Ejecucion

1. Descargue el archivo `practica.py` de este repositorio.
2. Abra una terminal, editor de codigio o IDE en la carpeta del archivo.
3. Ejecute el comando:
   ```bash
   python gui_string_ops.py
4. En su defecto solo ejecutar el .py desde el IDE o editor de codigo, instalando algunas extenciones en caso de ser necesarias dependiendo del programa para     ejecutar el codigo.
   
