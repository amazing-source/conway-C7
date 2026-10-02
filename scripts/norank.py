#!/usr/bin/env python3
"""Rank-free variant: use only positivity of the two integral 'projector' matrices
    G = 3C + 12I - 4J - 2uu^T   (G^2 = 21 G)
    H = 12I + 3J - 2uu^T - 4C   (H^2 = 28 H)
(both follow from (1)-(3) alone), i.e.  y^T G y >= 0, y^T H y >= 0, and
y^T G y = 0 => G y = 0 (same for H).  No trace / rank / eigenvalue-multiplicity input
beyond the zero diagonal.
"""
from fractions import Fraction as F
from itertools import product
from census6 import psd_rank, mixed_feasible

u = [1, 1, 1, -1, -1, -1] + [0] * 6

def Gent(i, j, c):  # c = C_ij (diag 0)
    return 3 * c + (12 if i == j else 0) - 4 - 2 * u[i] * u[j]

def Hent(i, j, c):
    return (12 if i == j else 0) + 3 - 2 * u[i] * u[j] - 4 * c

def kernel(M):
    """rational kernel basis of a square rational matrix"""
    n = len(M)
    A = [[F(x) for x in r] for r in M]
    piv_cols, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, n) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        pv = A[r][c]
        A[r] = [x / pv for x in A[r]]
        for i in range(n):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        piv_cols.append(c); r += 1
    free = [c for c in range(n) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [F(0)] * n; v[fc] = F(1)
        for i, pc in enumerate(piv_cols):
            v[pc] = -A[i][fc]
        basis.append(v)
    return basis

def blocks():
    rng = range(5)
    out = []
    for p01, p02, p12, q01, q02, q12 in product(rng, repeat=6):
        P = [[0, p01, p02], [p01, 0, p12], [p02, p12, 0]]
        Q = [[0, q01, q02], [q01, 0, q12], [q02, q12, 0]]
        rs = [sum(r) for r in P]; cs = [sum(r) for r in Q]
        if sum(rs) != sum(cs): continue
        rows = [[r for r in product(rng, repeat=3) if sum(r) == rs[i]] for i in range(3)]
        for r0 in rows[0]:
            for r1 in rows[1]:
                for r2 in rows[2]:
                    if any(r0[j] + r1[j] + r2[j] != cs[j] for j in range(3)): continue
                    R = [r0, r1, r2]
                    C6 = [[0] * 6 for _ in range(6)]
                    for i in range(3):
                        for j in range(3):
                            C6[i][j] = P[i][j]; C6[3 + i][3 + j] = Q[i][j]
                            C6[i][3 + j] = R[i][j]; C6[3 + j][i] = R[i][j]
                    ok = True
                    for i in range(6):
                        sig = sum(C6[i][j] for j in (range(3) if i < 3 else range(3, 6)))
                        sq = sum(C6[i][j] ** 2 for j in range(6))
                        if not mixed_feasible(12 - 2 * sig, 22 - sq): ok = False; break
                    if not ok: continue
                    G6 = [[Gent(i, j, C6[i][j]) for j in range(6)] for i in range(6)]
                    H6 = [[Hent(i, j, C6[i][j]) for j in range(6)] for i in range(6)]
                    if psd_rank(G6)[0] and psd_rank(H6)[0]:
                        out.append(C6)
    return out

def mixed_vectors(C6):
    G6 = [[Gent(i, j, C6[i][j]) for j in range(6)] for i in range(6)]
    H6 = [[Hent(i, j, C6[i][j]) for j in range(6)] for i in range(6)]
    kG, kH = kernel(G6), kernel(H6)
    res = []
    for x in product(range(5), repeat=6):
        if sum(x[:3]) != sum(x[3:]): continue
        g = [Gent(i, 6, x[i]) for i in range(6)]   # 3x-4
        hv = [Hent(i, 6, x[i]) for i in range(6)]  # 3-4x
        if any(sum(k[i] * g[i] for i in range(6)) != 0 for k in kG): continue
        if any(sum(k[i] * hv[i] for i in range(6)) != 0 for k in kH): continue
        MG = [row + [g[i]] for i, row in enumerate(G6)] + [g + [8]]
        MH = [row + [hv[i]] for i, row in enumerate(H6)] + [hv + [15]]
        if psd_rank(MG)[0] and psd_rank(MH)[0]:
            res.append(x)
    return res

if __name__ == '__main__':
    bl = blocks()
    hs = {}
    for C6 in bl:
        h = C6[0][1] + C6[0][2] + C6[1][2]
        hs[h] = hs.get(h, 0) + 1
    print("labelled blocks (G6,H6 PSD, no rank):", len(bl), "by h:", hs)
    dead = 0
    for C6 in bl:
        xs = mixed_vectors(C6)
        killer = None
        for r in range(6):
            vals = sorted({x[r] for x in xs})
            sig = sum(C6[r][j] for j in (range(3) if r < 3 else range(3, 6)))
            s, q = 12 - 2 * sig, 22 - sum(c * c for c in C6[r])
            if not any(sum(y) == s and sum(v * v for v in y) == q for y in product(vals, repeat=6)):
                killer = (r, vals, s, q); break
        if killer: dead += 1
        else:
            print("NOT KILLED by a single row:", C6, "num mixed vectors", len(xs))
    print("blocks killed by a single A/B row:", dead, "/", len(bl))
