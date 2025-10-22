
"""
Proyecto 2 – Teoría de la Computación (CFG → CNF + CYK + Parse Tree)
Autor: Luis Gonzalez, Diego Patzan, Roberto Nagera
Fecha: 2025-10-21

Descripción general
-------------------
Implementa:
1) Conversión de una gramática CFG a Forma Normal de Chomsky (CNF).
2) Algoritmo CYK (Cocke–Younger–Kasami) con programación dinámica.
3) Reconstrucción de un árbol de derivación para una cadena aceptada.
4) Medición del tiempo de ejecución del reconocimiento.

Uso
---
$ python proyecto2_cyk.py --demo
  Ejecuta casos de prueba predeterminados (aceptados, aceptados no semánticos y rechazados).

$ python proyecto2_cyk.py --sentence "she eats a cake with a fork"
  Valida la cadena contra la gramática por defecto (inglés simple).
  Muestra: ACEPTA/RECHAZA, tiempo, y un árbol de parseo si aplica.

$ python proyecto2_cyk.py --lower
  Fuerza a minúsculas la frase de entrada (útil si se ingresan palabras capitalizadas).

Notas
-----
- La gramática de ejemplo sigue el enunciado del proyecto: S→NP VP, VP→VP PP | V NP | cooks | ... etc.
- CYK requiere CNF; se implementa una conversión estándar: eliminación de ε (salvo posible S→ε),
  eliminación de unitarias, depuración de símbolos inútiles y binarización/terminalización.
- Para simplicidad de uso, se incluye una gramática por defecto en el propio archivo.
- Dependencias: solo biblioteca estándar de Python.

Estructura del código
---------------------
- CFG: Representación de gramática y utilidades de conversión a CNF.
- cnf_converter: rutina principal para transformar una CFG arbitraria en CNF.
- cyk_parse: implementación del algoritmo CYK con backpointers para reconstruir árboles.
- pretty_tree: impresión legible del árbol de derivación.
- main: interfaz de línea de comandos y casos de prueba.

Referencias clave
-----------------
- Proyecto 2 (PDF): "Implementar algoritmo de conversión a CNF y CYK; construir parse tree; medir tiempo".
- CYK: Wikipedia; textos clásicos de Lenguajes Formales y Autómatas.

"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Iterable, Optional
import argparse
import time


# ---------------------------
#   Representación de CFG
# ---------------------------

Symbol = str
Variable = str
Terminal = str
Rhs = Tuple[Symbol, ...]   # lado derecho de una producción, tupla de símbolos
ProductionMap = Dict[Variable, Set[Rhs]]


@dataclass
class CFG:
    variables: Set[Variable]
    terminals: Set[Terminal]
    start: Variable
    productions: ProductionMap  # A -> { (X,Y), (a,), ... }

    def copy(self) -> "CFG":
        return CFG(
            set(self.variables),
            set(self.terminals),
            self.start,
            {A: set(R) for A, R in self.productions.items()},
        )

    @staticmethod
    def from_rules(start: Variable, rules: Dict[Variable, Iterable[Iterable[Symbol]]]) -> "CFG":
        """Crea una CFG a partir de un dict {A: [[...], [...]], ...} con el símbolo inicial indicado.
        Se deducen variables y terminales según mayúsculas/minúsculas por convención:
          - Variables: claves del dict (A, S, NP, VP, ...)
          - Terminales: símbolos en minúscula o 'a','the','she','eats', etc., que no sean variables.
        """
        variables = set(rules.keys())
        productions: ProductionMap = {}
        terminals: Set[Terminal] = set()
        for A, rhss in rules.items():
            prset = productions.setdefault(A, set())
            for rhs in rhss:
                tup = tuple(rhs)
                prset.add(tup)
                for sym in tup:
                    if sym not in variables and sym != "ε":
                        terminals.add(sym)
        return CFG(variables=variables, terminals=terminals, start=start, productions=productions)

    def add_rule(self, A: Variable, rhs: Iterable[Symbol]) -> None:
        self.variables.add(A)
        tup = tuple(rhs)
        self.productions.setdefault(A, set()).add(tup)
        for sym in tup:
            if sym.islower() and sym not in self.variables:
                self.terminals.add(sym)

    def __str__(self) -> str:
        lines = [f"Start: {self.start}"]
        for A in sorted(self.productions.keys()):
            alts = [" ".join(rhs) if rhs else "ε" for rhs in sorted(self.productions[A])]
            lines.append(f"{A} → {' | '.join(alts)}")
        return "\n".join(lines)


# ---------------------------------------
#   Conversión CFG → CNF (estándar)
# ---------------------------------------

def cfg_to_cnf(cfg: CFG) -> CFG:
    """
    Convierte una CFG arbitraria a Forma Normal de Chomsky.
    Pasos (orden razonable):
      1) Asegurar que el start no aparezca en RHS (nuevo start S0 → S).
      2) Eliminar ε-producciones (excepto S0→ε si procede).
      3) Eliminar unitarias (A→B).
      4) Eliminar símbolos inútiles (no generadores / no alcanzables).
      5) Reemplazar terminales en RHS de longitud ≥ 2 por variables.
      6) Binarizar RHS largas a secuencias de 2.
    """
    g = cfg.copy()

    # 1) Nuevo símbolo inicial
    S0 = g.start + "₀"
    while S0 in g.variables:
        S0 += "₀"
    g.variables.add(S0)
    g.productions[S0] = { (g.start,) }
    g.start = S0

    # 2) ε-producciones
    nullable = compute_nullable(g)
    # Eliminar ε (excepto S0→ε si S original era nullable).
    new_productions: ProductionMap = {A: set() for A in g.productions}
    for A, rhss in g.productions.items():
        for rhs in rhss:
            if rhs == ("ε",):
                continue
            # Generar todas las combinaciones de eliminación de símbolos anulables
            expansions = eliminate_epsilon_from_rhs(rhs, nullable)
            for exp in expansions:
                if len(exp) == 0:
                    # Permitir ε solo para el nuevo start
                    if A == g.start:
                        new_productions[A].add(("ε",))
                else:
                    new_productions[A].add(tuple(exp))
    g.productions = new_productions

    # 3) Unitarias
    eliminate_unit_productions(g)

    # 4) Eliminar símbolos inútiles
    eliminate_useless_symbols(g)

    # 5) Terminalización en RHS largas
    # Mapear terminal 'a' -> variable especial Ta cuando aparezca en rhs de longitud ≥ 2
    term2var: Dict[Terminal, Variable] = {}
    for A, rhss in list(g.productions.items()):
        updated = set()
        for rhs in rhss:
            if len(rhs) >= 2:
                new_rhs = list(rhs)
                for i, sym in enumerate(rhs):
                    if sym in g.terminals:
                        if sym not in term2var:
                            Tv = f"T_{sym}"
                            # evitar colisiones
                            idx = 1
                            while Tv in g.variables:
                                idx += 1
                                Tv = f"T_{sym}_{idx}"
                            g.variables.add(Tv)
                            g.productions.setdefault(Tv, set()).add((sym,))
                            term2var[sym] = Tv
                        new_rhs[i] = term2var[sym]
                updated.add(tuple(new_rhs))
            else:
                updated.add(rhs)
        g.productions[A] = updated

    # 6) Binarización
    binarize(g)

    # Actualizar conjunto de terminales (por si se crearon nuevas variables T_x)
    g.terminals = set()
    for A, rhss in g.productions.items():
        for rhs in rhss:
            for sym in rhs:
                if sym not in g.variables and sym != "ε":
                    g.terminals.add(sym)
    return g


def compute_nullable(g: CFG) -> Set[Variable]:
    """Conjunto de variables que derivan ε."""
    nullable: Set[Variable] = set()
    changed = True
    while changed:
        changed = False
        for A, rhss in g.productions.items():
            if A in nullable:
                continue
            for rhs in rhss:
                if rhs == ("ε",):
                    nullable.add(A); changed = True; break
                if all(sym in nullable for sym in rhs):
                    nullable.add(A); changed = True; break
    return nullable


def eliminate_epsilon_from_rhs(rhs: Rhs, nullable: Set[Variable]) -> Set[Tuple[Symbol, ...]]:
    """Todas las expansiones de rhs eliminando ocurrencias de variables anulables (no todas a la vez)."""
    results: Set[Tuple[Symbol, ...]] = set()
    n = len(rhs)
    # backtracking sobre subconjuntos de posiciones anulables
    def bt(i: int, acc: List[Symbol]):
        if i == n:
            results.add(tuple(acc))
            return
        sym = rhs[i]
        if sym in nullable:
            # opción 1: omitir
            bt(i+1, acc)
        # opción 2: conservar
        acc.append(sym)
        bt(i+1, acc)
        acc.pop()
    bt(0, [])
    # quitar la expansión vacía; se maneja por el llamador para S0
    results.discard(tuple())
    return results


def eliminate_unit_productions(g: CFG) -> None:
    """Elimina A→B (unitarias), cerrando por implicación A⇒*B⇒α y agregando A→α si corresponde."""
    unit_graph: Dict[Variable, Set[Variable]] = {A: set() for A in g.productions}
    new_prods: ProductionMap = {A: set() for A in g.productions}
    # Separar unitarias y no unitarias
    for A, rhss in g.productions.items():
        for rhs in rhss:
            if len(rhs) == 1 and rhs[0] in g.variables:
                unit_graph[A].add(rhs[0])
            else:
                new_prods[A].add(rhs)
    # Clausura transitiva
    closure: Dict[Variable, Set[Variable]] = {A: set() for A in g.productions}
    for A in g.productions:
        stack = [A]
        seen = set()
        while stack:
            X = stack.pop()
            for Y in unit_graph.get(X, ()):
                if Y not in seen:
                    seen.add(Y)
                    stack.append(Y)
        closure[A] = seen
    # Agregar producciones no unitarias heredadas
    for A in g.productions:
        for B in closure[A]:
            for rhs in g.productions.get(B, ()):
                if not (len(rhs) == 1 and rhs[0] in g.variables):
                    new_prods[A].add(rhs)
    g.productions = new_prods


def eliminate_useless_symbols(g: CFG) -> None:
    """Elimina símbolos no generadores/no alcanzables."""
    # 1) Generadores: variables que derivan alguna cadena de terminales
    generating: Set[Variable] = set()
    changed = True
    while changed:
        changed = False
        for A, rhss in g.productions.items():
            if A in generating:
                continue
            for rhs in rhss:
                if all(sym in g.terminals or sym == "ε" or sym in generating for sym in rhs):
                    generating.add(A); changed = True; break
    # Filtrar por generadores
    g.productions = {A: {rhs for rhs in rhss if all(sym in g.terminals or sym == "ε" or sym in generating for sym in rhs)}
                     for A, rhss in g.productions.items() if A in generating}
    g.variables = set(g.productions.keys())

    # 2) Alcanzables desde S
    reachable: Set[Symbol] = {g.start}
    changed = True
    while changed:
        changed = False
        for A, rhss in g.productions.items():
            if A in reachable:
                for rhs in rhss:
                    for sym in rhs:
                        if sym not in reachable and (sym in g.variables or sym in g.terminals or sym == "ε"):
                            reachable.add(sym); changed = True
    # Filtrar por alcanzables
    g.productions = {A: {rhs for rhs in rhss if all(sym in reachable or sym == "ε" for sym in rhs)}
                     for A, rhss in g.productions.items() if A in reachable}
    g.variables = set(g.productions.keys())



def binarize(g: CFG) -> None:
    """Convierte RHS de longitud > 2 en reglas binarias introduciendo variables auxiliares.
    Resultado: todas las producciones tienen RHS de longitud 1 (terminal) o 2 (variables).
    """
    final_prods: ProductionMap = {A: set() for A in g.productions}
    counter = 1

    for A, rhss in g.productions.items():
        for rhs in rhss:
            if len(rhs) <= 2:
                final_prods[A].add(rhs)
                continue

            # rhs = (s1, s2, ..., sk), k >= 3
            symbols = list(rhs)
            # Crearemos variables auxiliares BIN_1, BIN_2, ...
            prev_var = A
            for i in range(len(symbols) - 2):
                left_sym = symbols[i]
                # Si aún quedan más de 2 símbolos por procesar, creamos aux
                if i < len(symbols) - 3:
                    aux = f"BIN_{counter}"
                    counter += 1
                    while aux in g.variables:
                        aux = f"BIN_{counter}"
                        counter += 1
                    g.variables.add(aux)
                    final_prods[prev_var].add((left_sym, aux))
                    prev_var = aux
                else:
                    # último paso: agregar (s_{k-1}, s_k) bajo prev_var
                    final_prods[prev_var].add((left_sym, symbols[i+1]))

    g.productions = final_prods
# ---------------------------------------
#   Algoritmo CYK + backpointers
# ---------------------------------------

BackPtr = Tuple[str, Optional[Tuple[int,int,int]], Optional[str], Optional[str], Optional[str]]
# (rule_type, split_triple, left_var, right_var, terminal)
# rule_type: "TERM" o "BIN"


def cyk_parse(cnf: CFG, tokens: List[str]) -> Tuple[bool, Dict[Tuple[int,int,Variable], BackPtr]]:
    """
    Devuelve (acepta, backpointers) sobre una gramática en CNF.
    backpointers almacena, para cada celda (i,j,A), una explicación de cómo se derivó.
    """
    n = len(tokens)
    if n == 0:
        # Acepta si S -> ε existe
        accepts = ("ε",) in cnf.productions.get(cnf.start, set())
        return accepts, {}

    # Tabla CYK: T[i][j] = set de variables que generan w[i:j+1]
    T: List[List[Set[Variable]]] = [[set() for _ in range(n)] for _ in range(n)]
    back: Dict[Tuple[int,int,Variable], BackPtr] = {}

    # Preprocesar producciones inversas
    term_to_vars: Dict[str, Set[Variable]] = {}
    bin_to_vars: Dict[Tuple[str,str], Set[Variable]] = {}

    for A, rhss in cnf.productions.items():
        for rhs in rhss:
            if len(rhs) == 1 and rhs[0] in cnf.terminals:
                term_to_vars.setdefault(rhs[0], set()).add(A)
            elif len(rhs) == 2 and rhs[0] in cnf.variables and rhs[1] in cnf.variables:
                bin_to_vars.setdefault((rhs[0], rhs[1]), set()).add(A)
            elif rhs == ("ε",):
                # permitido sólo para S; el caso n==0 ya se atendió.
                pass

    # Inicialización: longitud 1
    for i, tok in enumerate(tokens):
        for A in term_to_vars.get(tok, ()):
            T[i][i].add(A)
            back[(i, i, A)] = ("TERM", None, None, None, tok)

    # Caso longitud >= 2
    for span in range(2, n+1):  # longitud del segmento
        for i in range(0, n-span+1):
            j = i + span - 1
            for k in range(i, j):
                left_set = T[i][k]
                right_set = T[k+1][j]
                if not left_set or not right_set:
                    continue
                for B in left_set:
                    for C in right_set:
                        for A in bin_to_vars.get((B, C), ()):
                            if A not in T[i][j]:
                                T[i][j].add(A)
                                back[(i, j, A)] = ("BIN", (i, k, j), B, C, None)

    accepts = cnf.start in T[0][n-1]
    return accepts, back


# ---------------------------------------
#   Reconstrucción de árbol
# ---------------------------------------

@dataclass
class Node:
    symbol: str
    children: List["Node"] = field(default_factory=list)

    def to_brackets(self) -> str:
        if not self.children:
            return self.symbol
        return "(" + self.symbol + " " + " ".join(ch.to_brackets() for ch in self.children) + ")"

    def pretty(self, indent: str = "", is_last: bool = True) -> str:
        branch = "└── " if is_last else "├── "
        s = indent + branch + self.symbol + "\n"
        new_indent = indent + ("    " if is_last else "│   ")
        for idx, ch in enumerate(self.children):
            s += ch.pretty(new_indent, idx == len(self.children) - 1)
        return s


def build_parse_tree(tokens: List[str], back: Dict[Tuple[int,int,Variable], BackPtr], i: int, j: int, A: Variable) -> Optional[Node]:
    """Reconstruye *un* árbol de derivación para (i,j,A) usando backpointers."""
    key = (i, j, A)
    if key not in back:
        return None
    rule_type, split_triple, B, C, term = back[key]
    if rule_type == "TERM":
        # A -> term
        return Node(A, [Node(term)])
    elif rule_type == "BIN" and split_triple is not None:
        i0, k, j0 = split_triple
        # Elegir un árbol válido para B en (i, k) y C en (k+1, j)
        left = build_any_tree(tokens, back, i0, k, B)
        right = build_any_tree(tokens, back, k+1, j0, C)
        if left and right:
            return Node(A, [left, right])
    return None


def build_any_tree(tokens: List[str], back: Dict[Tuple[int,int,Variable], BackPtr], i: int, j: int, target_var: Optional[Variable] = None) -> Optional[Node]:
    """Intenta construir un árbol en la celda (i,j) escogiendo cualquier variable que tenga backpointer.
    Si se indica target_var, busca un árbol específicamente para esa variable."""
    if target_var is not None:
        return build_parse_tree(tokens, back, i, j, target_var)

    # Intentar con cualquiera: preferimos el start si coincide con el segmento completo
    candidates = [A for (ii,jj,A) in back.keys() if ii == i and jj == j]
    # orden estable: por longitud descendente del símbolo, para consistencia
    for A in sorted(candidates, key=lambda x: len(x), reverse=True):
        node = build_parse_tree(tokens, back, i, j, A)
        if node is not None:
            return node
    return None


# ---------------------------------------
#   Gramática por defecto (del enunciado)
# ---------------------------------------

def default_cfg() -> CFG:
    # Gramática del enunciado (CFG de inglés simple)
    # Notación: variables en mayúsculas/mixtas; terminales en minúsculas.
    rules = {
        "S": [["NP", "VP"]],
        "VP": [["VP", "PP"], ["V", "NP"], ["cooks"], ["drinks"], ["eats"], ["cuts"]],
        "PP": [["P", "NP"]],
        "NP": [["Det", "N"], ["he"], ["she"]],
        "V": [["cooks"], ["drinks"], ["eats"], ["cuts"]],
        "P": [["in"], ["with"]],
        "N": [["cat"], ["dog"], ["beer"], ["cake"], ["juice"], ["meat"], ["soup"], ["fork"], ["knife"], ["oven"], ["spoon"]],
        "Det": [["a"], ["the"]],
    }
    return CFG.from_rules(start="S", rules=rules)


# ---------------------------------------
#   Utilidades de presentación
# ---------------------------------------

def pretty_grammar(g: CFG, title: str = "Gramática") -> str:
    lines = [title, "=" * len(title), f"Start: {g.start}", "Producciones:"]
    for A in sorted(g.productions.keys()):
        alts = []
        for rhs in sorted(g.productions[A]):
            if rhs == ("ε",):
                alts.append("ε")
            else:
                alts.append(" ".join(rhs))
        lines.append(f"  {A} → " + " | ".join(alts))
    return "\n".join(lines)


def time_cyk(cnf: CFG, sentence: str, force_lower: bool = False) -> Tuple[bool, float, Optional[Node]]:
    tokens = sentence.strip().split()
    if force_lower:
        tokens = [t.lower() for t in tokens]
    t0 = time.perf_counter()
    accepts, back = cyk_parse(cnf, tokens)
    elapsed = time.perf_counter() - t0
    tree = None
    if accepts:
        tree = build_parse_tree(tokens, back, 0, len(tokens) - 1, cnf.start)
    return accepts, elapsed, tree


# ---------------------------------------
#   Casos de prueba del informe
# ---------------------------------------

def demo_cases(force_lower: bool = True) -> None:
    cfg = default_cfg()
    cnf = cfg_to_cnf(cfg)

    print(pretty_grammar(cfg, "CFG original"))
    print()
    print(pretty_grammar(cnf, "CNF derivada"))
    print()

    # 2 aceptadas y semánticamente correctas
    accepted_semantic = [
        "she eats a cake",
        "the cat drinks the juice",
    ]
    # 2 aceptadas pero semánticamente raras (la gramática no verifica semántica)
    accepted_weird = [
        "she cuts the soup",
        "the dog drinks a fork",
    ]
    # 2 no aceptadas por la gramática
    rejected = [
        "she the eats cake",
        "they eat a cake",  # "they" y "eat" no están en la gramática
    ]

    groups = [
        ("Aceptadas (semánticamente correctas)", accepted_semantic),
        ("Aceptadas (no semánticamente correctas)", accepted_weird),
        ("Rechazadas (no pertenecen al lenguaje)", rejected),
    ]

    for title, sentences in groups:
        print("=" * 80)
        print(title)
        print("=" * 80)
        for s in sentences:
            ok, t, tree = time_cyk(cnf, s, force_lower=force_lower)
            print(f'Frase: "{s}"')
            print(f"Resultado: {'SI' if ok else 'NO'}")
            print(f"Tiempo: {t*1000:.3f} ms")
            if ok and tree is not None:
                print("Árbol (notación bracketed):")
                print(tree.to_brackets())
                print("Árbol (pretty):")
                print(tree.pretty().rstrip())
            print("-" * 80)


# ---------------------------------------
#   CLI
# ---------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Proyecto 2: CFG→CNF + CYK + Parse Tree")
    parser.add_argument("--sentence", "-s", type=str, default=None, help="Frase a validar")
    parser.add_argument("--demo", action="store_true", help="Ejecuta casos de prueba predefinidos")
    parser.add_argument("--lower", action="store_true", help="Fuerza a minúsculas la frase de entrada")
    args = parser.parse_args()

    cfg = default_cfg()
    cnf = cfg_to_cnf(cfg)

    if args.demo or args.sentence is None:
        demo_cases(force_lower=True or args.lower)
        return

    s = args.sentence
    ok, elapsed, tree = time_cyk(cnf, s, force_lower=args.lower)
    print("=" * 80)
    print(f'Frase: "{s}"')
    print(f"Resultado: {'SI' if ok else 'NO'}")
    print(f"Tiempo: {elapsed*1000:.3f} ms")
    if ok and tree is not None:
        print("Árbol (notación bracketed):")
        print(tree.to_brackets())
        print("Árbol (pretty):")
        print(tree.pretty().rstrip())
    print("=" * 80)


if __name__ == "__main__":
    main()