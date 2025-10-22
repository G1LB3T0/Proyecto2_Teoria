
# Proyecto 2 – Teoría de la Computación (CFG→CNF + CYK + Parse Tree)

Este paquete implementa:
1) Conversión de una gramática CFG a **Forma Normal de Chomsky (CNF)**.
2) Algoritmo **CYK** con programación dinámica para decidir pertenencia de una cadena.
3) **Reconstrucción de un árbol de derivación** para cadenas aceptadas.
4) Medición de **tiempo de ejecución** de la validación.

## Enunciado de referencia
El desarrollo sigue los requerimientos del documento “Proyecto 2” (10.sep.2025), que pide:
- Implementar conversión CFG→CNF.
- Implementar CYK para decidir si una oración inglesa simple pertenece al lenguaje.
- Reportar **SI/NO**, **tiempo** y **parse tree**.
- Proveer ejemplos aceptados (semánticamente plausibles e implausibles) y rechazados.

## Requisitos
- Python 3.9+
- Sin dependencias externas (solo biblioteca estándar).

## Archivos
- `proyecto2_cyk.py` — Implementación completa (CFG, CNF, CYK, parse tree y CLI).
- Este `README_Proyecto2.md`.

## Uso rápido
```bash
python proyecto2_cyk.py --demo
```
Muestra la gramática por defecto, su CNF, y ejecuta 6 frases de prueba:  
- 2 aceptadas y semánticamente correctas  
- 2 aceptadas pero semánticamente incorrectas  
- 2 rechazadas

Validar una frase concreta:
```bash
python proyecto2_cyk.py --sentence "She eats a cake with a fork" --lower
```

**Nota sobre mayúsculas:** la gramática usa terminales en minúsculas. Use `--lower` para bajar la frase a minúsculas.

## Diseño y decisiones
- **Representación:** `CFG` con `productions: Dict[Variable, Set[Tuple[Symbol,...]]]`.
- **CNF:** se aplican pasos estándar: `S0→S`, eliminación de `ε` (manteniendo `S0→ε` si corresponde), eliminación de unitarias,
  depuración de símbolos inútiles (no generadores y no alcanzables), terminalización en reglas largas y binarización.
- **CYK:** tabla triangular `T[i][j]` con conjuntos de variables y **backpointers** para reconstrucción de un árbol.
- **Árbol:** se entrega en notación **bracketed** y en un **dibujo ASCII**.

## Discusión
- La gramática de ejemplo permite frases sintácticamente correctas que pueden carecer de sentido semántico
  (por ejemplo, “the dog drinks a fork”); esto es esperado y se documenta en las pruebas.
- La conversión a CNF introduce variables auxiliares (`T_<terminal>`, `BIN_<n>`), y puede crecer el número de reglas.
- Para mantener el script autocontenido, la gramática del enunciado se codifica directamente en el archivo.

## Pruebas incluidas
Ejecute `--demo` para observar resultados con tiempos y árboles.
- **Aceptadas semánticamente correctas:** “she eats a cake”, “the cat drinks the juice”.
- **Aceptadas no semánticamente correctas:** “she cuts the soup”, “the dog drinks a fork”.
- **Rechazadas:** “she the eats cake”, “they eat a cake”.

## Extensiones sugeridas
- Exportar árboles a formato Graphviz.
- Soportar gramáticas cargadas desde JSON/YAML.
- Enumerar múltiples árboles si la oración es ambigua.

## Licencia
Uso académico.
