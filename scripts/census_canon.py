#!/usr/bin/env python3
"""Census for canonical (P,Q) via the Lean strategy:
column b1 admissible (alpha>0) -> factor with S=(0,1,2,3) -> equations at (4,4),(4,5),(5,5).
Report surviving R and whether any need a row-feasibility certificate."""
import itertools, sympy as sp
from census6 import mixed_feasible
from gen_lean import Gent, block_from

T = {'111': [[0,1,1],[1,0,1],[1,1,0]], '112': [[0,1,1],[1,0,2],[1,2,0]],
     '113': [[0,1,1],[1,0,3],[1,3,0]], '122': [[0,1,2],[1,0,2],[2,2,0]]}
pairs = [('111','111'), ('112','112'), ('113','113'), ('113','122'), ('122','113'), ('122','122')]
for pn, qn in pairs:
    P, Q = T[pn], T[qn]
    sA = [sum(r) for r in P]; sB = [sum(r) for r in Q]
    cols = {b: [c for c in itertools.product(range(5), repeat=3) if sum(c) == sB[b]] for b in range(3)}
    surv = []; nleaf = 0; nneg = 0
    for c0 in cols[0]:
        # alpha for column b1 via det of G_{A u b1}
        R0 = [[c0[a], 0, 0] for a in range(3)]
        C6 = block_from(P, Q, R0)
        G = [[Gent(i, j, C6[i][j]) for j in range(6)] for i in range(6)]
        M = sp.Matrix([[G[i][j] for j in (0,1,2,3)] for i in (0,1,2,3)])
        d = M.det()
        if d <= 0:
            nneg += 1
            continue
        for c1 in cols[1]:
            for c2 in cols[2]:
                nleaf += 1
                R = [[c0[a], c1[a], c2[a]] for a in range(3)]
                if any(sum(R[a]) != sA[a] for a in range(3)): continue
                C6 = block_from(P, Q, R)
                G = [[Gent(i, j, C6[i][j]) for j in range(6)] for i in range(6)]
                Gm = sp.Matrix(G)
                # rank-4 factorization through S=(0,1,2,3)
                S = [0,1,2,3]
                GS = Gm.extract(S, S); Gc = Gm.extract(list(range(6)), S)
                ok = (Gc * GS.inv() * Gc.T - Gm) == sp.zeros(6, 6)
                if not ok: continue
                feas = all(mixed_feasible(12 - sum(C6[r]), 22 - sum(x*x for x in C6[r])) for r in range(6))
                surv.append((R, feas))
    print(pn, qn, "col b1 options", len(cols[0]), "with det<=0:", nneg, "leaves", nleaf, "survivors", len(surv))
    for R, feas in surv: print("   ", R, "row-feasible" if feas else "ROW-INFEASIBLE")
