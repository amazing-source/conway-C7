#!/usr/bin/env python3
"""Data for the hand derivation of the mixed vectors in the six cases:
integer kernel relations of G6, and the norm form on a 4-subset basis."""
from fractions import Fraction as F
from itertools import product
from math import gcd
from norank import kernel
from census6 import gram6
from mixed6 import cases

def lcm(a, b): return a * b // gcd(a, b)

def inv(M):
    n = len(M); A = [[F(x) for x in r] + [F(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]; A[c] = [x / pv for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]; A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return [r[n:] for r in A]

names = ['a1', 'a2', 'a3', 'b1', 'b2', 'b3']
for k, C6 in cases.items():
    G6 = gram6(C6)
    ker = kernel(G6)
    rels = []
    for v in ker:
        L = 1
        for x in v: L = lcm(L, x.denominator)
        w = [int(x * L) for x in v]
        g = 0
        for x in w: g = gcd(g, abs(x))
        rels.append([x // g for x in w])
    print(f"case {k}: C6 rows {C6}")
    print("   kernel relations (sum w_i v_i = 0):", rels)
    # choose basis = first 4 independent indices among a1,a2,b1,b2 or similar
    for S in [(0, 1, 3, 4), (0, 1, 2, 3), (0, 1, 3, 5), (0, 2, 3, 4), (1, 2, 4, 5)]:
        GS = [[G6[i][j] for j in S] for i in S]
        try:
            Gi = inv(GS)
        except StopIteration:
            continue
        print("   basis", [names[i] for i in S], "G_S =", GS)
        print("   G_S^{-1} =", [[str(x) for x in r] for r in Gi])
        break
