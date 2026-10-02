#!/usr/bin/env python3
"""Mixed-attachment vectors for the six first-six cases (candidate's representatives).

For a mixed orbit m, x = (C_{m,a})_{a in A u B}.  Necessary: x in {0..4}^6,
sum_A x = sum_B x (row m of Cu=0), and the 7x7 Gram matrix
   [[G6, g], [g^T, 8]],  g = 3x - 4,
is PSD of rank 4 (all 12 Gram vectors live in a 4-space spanned by v_1..v_6).
"""
from itertools import product
from census6 import psd_rank, gram6

def sym(P, Q, R):
    C6 = [[0] * 6 for _ in range(6)]
    for i in range(3):
        for j in range(3):
            C6[i][j] = P[i][j]; C6[3 + i][3 + j] = Q[i][j]
            C6[i][3 + j] = R[i][j]; C6[3 + j][i] = R[i][j]
    return C6

T = [[0, 1, 1], [1, 0, 1], [1, 1, 0]]
cases = {
    1: sym(T, T, [[0, 0, 2], [0, 2, 0], [2, 0, 0]]),
    2: sym(T, T, [[0, 0, 2], [1, 1, 0], [1, 1, 0]]),
    3: sym(T, T, T),
    4: sym([[0, 1, 1], [1, 0, 2], [1, 2, 0]], [[0, 1, 1], [1, 0, 2], [1, 2, 0]], [[0, 1, 1], [1, 0, 2], [1, 2, 0]]),
    5: sym([[0, 1, 1], [1, 0, 3], [1, 3, 0]], [[0, 1, 1], [1, 0, 3], [1, 3, 0]], [[0, 1, 1], [1, 1, 2], [1, 2, 1]]),
    6: sym([[0, 1, 2], [1, 0, 2], [2, 2, 0]], [[0, 1, 2], [1, 0, 2], [2, 2, 0]], [[0, 1, 2], [1, 2, 0], [2, 0, 2]]),
}

for k, C6 in cases.items():
    G6 = gram6(C6)
    psd, rk = psd_rank(G6)
    assert psd and rk == 4, (k, psd, rk)
    # sanity: the block satisfies P1=R1, R^T1=Q1
    for i in range(3):
        assert sum(C6[i][0:3]) == sum(C6[i][3:6])
        assert sum(C6[3 + i][0:3]) == sum(C6[3 + i][3:6])
    xs = []
    for x in product(range(5), repeat=6):
        if sum(x[:3]) != sum(x[3:]):
            continue
        g = [3 * xi - 4 for xi in x]
        M = [row + [g[i]] for i, row in enumerate(G6)] + [g + [8]]
        ok, r = psd_rank(M)
        if ok and r == 4:
            xs.append(x)
    vals = sorted({x[0] for x in xs})
    row = C6[0]
    sig = sum(row[0:3])
    s, q = 12 - 2 * sig, 22 - sum(c * c for c in row)
    # can six values from `vals` have sum s and square-sum q?
    feas = [y for y in product(vals, repeat=6) if sum(y) == s and sum(v * v for v in y) == q]
    print(f"case {k}: #mixed vectors={len(xs)} {xs}")
    print(f"        C_(m,A1) in {vals};  row A1 needs mixed sum {s}, square-sum {q};  feasible 6-tuples: {len(feas)}")
