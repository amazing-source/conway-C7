#!/usr/bin/env python3
"""Hand-style derivation of the A/B block for h = 4, 5 (residual method).

A-vectors v_a1,v_a2,v_a3 span a 3-space U (G_A nonsingular).  For b in B write
v_b = p_b + z_b n  (n a unit normal to U in R^4).  Then
   |p_b|^2 = X_b^T G_A^{-1} X_b,   X_b = 3 R[:,b] - 2,   z_b^2 = 6 - |p_b|^2,
   sum_b z_b = 0  (since sum_B v_b = sum_A v_a lies in U),
   v_b.v_b' = p_b.p_b' + z_b z_b'.
"""
from fractions import Fraction as F
from itertools import product, permutations

def inv3(M):
    a, b, c = M[0]; d, e, f = M[1]; g, h, i = M[2]
    det = a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)
    adj = [[e*i-f*h, c*h-b*i, b*f-c*e], [f*g-d*i, a*i-c*g, c*d-a*f], [d*h-e*g, b*g-a*h, a*e-b*d]]
    return det, [[F(adj[r][s], det) for s in range(3)] for r in range(3)]

def gramA(w12, w13, w23):
    return [[6, 3*w12-6, 3*w13-6], [3*w12-6, 6, 3*w23-6], [3*w13-6, 3*w23-6, 6]]

def qf(X, M, Y):
    return sum(X[r]*M[r][s]*Y[s] for r in range(3) for s in range(3))

types = {  # canonical labelling: (w12, w13, w23)
    '112': (1, 1, 2), '113': (1, 1, 3), '122': (2, 2, 1),
}
def rowsums(w):
    w12, w13, w23 = w
    return (w12 + w13, w12 + w23, w13 + w23)

for tp in types:
    for tq in types:
        wp, wq = types[tp], types[tq]
        if sum(wp) != sum(wq): continue
        GA = gramA(*wp); det, GAi = inv3(GA)
        sA, sB = rowsums(wp), rowsums(wq)
        GB = gramA(*wq)
        print(f"P type {tp} (row sums {sA}), Q type {tq} (row sums {sB}); det G_A = {det}")
        # admissible columns per b
        cols = {}
        for b in range(3):
            cols[b] = []
            for c in product(range(5), repeat=3):
                if sum(c) != sB[b]: continue
                X = [3*ci - 2 for ci in c]
                z2 = 6 - qf(X, GAi, X)
                if z2 >= 0:
                    cols[b].append((c, z2))
            print(f"   b{b+1} (col sum {sB[b]}): " + ", ".join(f"{c}:z^2={z2}" for c, z2 in cols[b]))
        sols = []
        for (c0, z0), (c1, z1), (c2, z2) in product(cols[0], cols[1], cols[2]):
            R = [[c0[a], c1[a], c2[a]] for a in range(3)]
            if any(sum(R[a]) != sA[a] for a in range(3)): continue
            # p_b . p_b' and residual products
            Xs = [[3*c - 2 for c in col] for col in (c0, c1, c2)]
            zz = [z0, z1, z2]
            # need real z_b with z_b^2 = zz[b], sum z_b = 0, z_b z_b' = G_bb' - p_b.p_b'
            ok = True
            prod_needed = {}
            for b in range(3):
                for bp in range(b+1, 3):
                    prod_needed[(b, bp)] = GB[b][bp] - qf(Xs[b], GAi, Xs[bp])
                    if prod_needed[(b, bp)] ** 2 != zz[b] * zz[bp]: ok = False
            if not ok: continue
            # sum z = 0 : (sum z)^2 = sum z^2 + 2 sum z_b z_b' = 0
            if sum(zz) + 2 * sum(prod_needed.values()) != 0: continue
            sols.append((R, zz))
        for R, zz in sols:
            print(f"   -> R = {R}, residual z^2 = {zz}")
        if not sols: print("   -> no R")
