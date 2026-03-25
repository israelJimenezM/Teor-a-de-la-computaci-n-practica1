# Simulador de Autómatas Finitos Deterministas (AFD)
Esta practica es una herramienta con interfaz grafica (GUI) desarrollada en Python con el framework Flet para construir, importar, simular, visualizar y exportar Autómatas Finitos Deterministas (AFD). Además permite realizar analisis de estructuras de cadenas y calculos de cerraduras de Kleene y Positivas.
---
## Requerimientos del Sistema
Para ejecutar este programa, asegurese de cumplir con lo siguiente:
* **Lenguaje:** Python 3.14.3, version 3.8 o superior recomendada.
* **Librerias:**
    * flet 0.82.2: instalar con `pip install flet==0.82.2`
    * tkinter: Viene preinstalada con Python en Windows y macOS.
        * Nota para usuarios de Linux (Ubuntu/Debian): Si no la tiene, instalela con `sudo apt-get install python3-tk`.
* **Hardware:** No requiere hardware especial, pero tenga en cuenta que la generacion masiva de cadenas consume memoria RAM.
---
## Guia de Uso por Pestañas
La aplicacion organiza sus funciones en siete secciones principales:
### 1. Pestaña: Definición
En esta seccion puede construir un AFD desde cero llenando todos los componentes de la quintupla formal.
* **Entrada:** Ingrese los estados y el alfabeto separados por coma (ej: q0, q1, q2 / a, b).
* **Accion:** Presione «1. Generar tabla» para crear la tabla de transiciones editable.
* **Configuracion:** Seleccione el estado inicial y marque los estados de aceptacion con las casillas.
* **Guardar:** Presione «2. Guardar AFD» para validar y confirmar el automata.
### 2. Pestaña: Importar
En esta seccion puede cargar un AFD previamente guardado desde un archivo. Utiliza el dialogo nativo de Windows (tkinter) para seleccionar el archivo.
* **Entrada:** Presione «Cargar archivo» y seleccione un archivo .jff, .json o .xml valido.
* **Resultados:** Los componentes detectados (alfabeto, estados, transiciones) se muestran automaticamente.
* **Nota:** El AFD cargado queda disponible en todas las demas pestanas.
### 3. Pestaña: Simulación
Permite validar cadenas sobre el AFD activo con traza completa y navegacion paso a paso.
* **Entrada:** Escriba la cadena a validar en el campo de texto.
* **Resultados:** Se muestra si la cadena es ACEPTADA o RECHAZADA, junto con la traza: δ(estado, símbolo) = siguiente_estado.
* **Accion:** Use los botones ⏮ ⏭ 🔄 para recorrer la simulacion paso a paso.
### 4. Pestaña: Visual
Muestra un resumen visual del AFD activo: estados con indicadores, tabla de transiciones completa y metadatos del automata.
* Los estados iniciales se indican con → y los de aceptacion con ✓.
* Esta pestana se actualiza automaticamente al guardar o importar un AFD.
* Para diagramas completos, exporte a .jff y abralo en JFLAP.
### 5. Pestaña: Exportar
Permite exportar el AFD activo a cualquiera de los tres formatos soportados.
* **Accion:** Presione «Ver / Guardar .jff», «.json» o «.xml» para previsualizar el contenido.
* **Guardar:** Presione «Guardar archivo» para elegir el destino en el explorador de Windows.
* **Nota:** Los archivos .jff son compatibles con el software JFLAP.
### 6. Pestaña: Subcadenas
En esta seccion puede analizar la estructura interna de una cadena.
* **Entrada:** Escriba una palabra (ej. hola).
* **Resultados:** Se muestran tres columnas independientes:
    * **Prefijos:** Todas las cadenas iniciales posibles.
    * **Sufijos:** Todas las cadenas finales posibles.
    * **Subcadenas:** Todas las combinaciones contiguas unicas, ordenadas por aparicion.
* **Accion:** Boton para exportar los resultados en un archivo .txt.
### 7. Pestaña: Kleene (Σ*, Σ+)
Seccion dedicada a la generacion de lenguajes formales.
* **Entrada:** Introduce un alfabeto (ej: 0,1 o abc) y la longitud maxima $n$, o usa el alfabeto del AFD activo.
* **Resultados:**
    * **Σ* (Kleene):** Genera el conjunto de todas las cadenas de longitud 0 hasta $n$.
    * **Σ+ (Positiva):** Genera el conjunto de todas las cadenas de longitud 1 hasta $n$.
* **Seguridad:** El programa muestra un aviso si la generacion excede las 20,000 cadenas para proteger la estabilidad de su sistema.
* **Accion:** Boton para exportar los resultados en un archivo .txt.
---
## Instrucciones de Ejecucion
1. Descargue el archivo `practica2.py` de este repositorio.
2. Abra una terminal, editor de codigo o IDE en la carpeta del archivo.
3. Ejecute el comando:
```bash
   py practica2.py
```
4. En su defecto solo ejecutar el .py desde el IDE o editor de codigo, instalando algunas extensiones en caso de ser necesarias dependiendo del programa para ejecutar el codigo.
