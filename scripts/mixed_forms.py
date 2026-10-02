#!/usr/bin/env python3
"""Symbolic form of the mixed-vector conditions in the six cases (sympy)."""
import sympy as sp
from mixed6 import cases
from census6 import gram6

xs = sp.symbols('x1 x2 x3 y1 y2 y3', integer=True)   # x = attachments to a1..a3, y = to b1..b3
for k, C6 in cases.items():
    G6 = sp.Matrix(gram6(C6))
    g = sp.Matrix([3 * v - 4 for v in xs])
    ker = G6.nullspace()
    lin = [sp.expand((kv.T * g)[0] * sp.lcm([t.q for t in kv])) for kv in ker]
    lin.append(sp.expand(sum(xs[:3]) - sum(xs[3:])))
    sol = sp.solve(lin, [xs[2], xs[5], xs[3]], dict=True)
    # basis: choose 4 indices with nonsingular block
    import itertools
    for S in itertools.combinations(range(6), 4):
        GS = G6.extract(list(S), list(S))
        if GS.det() != 0: break
    gS = g.extract(list(S), [0])
    norm = sp.expand(((gS.T * GS.inv() * gS)[0]))
    print(f"case {k}: linear conditions {lin}")
    for s in sol:
        nn = sp.factor(sp.expand(norm.subs(s)) - 8)
        print(f"   solved {s};  norm-8 = {nn}")
