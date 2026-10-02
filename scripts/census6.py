#!/usr/bin/env python3
"""Independent exact re-derivation of the first-six census (LL/RR block of C).

Uses only necessary conditions derived from (1)-(3) + zero diagonal:
  * C symmetric, entries 0..4, zero diagonal
  * Cu = 0 on rows of A,B:  P1 = R1,  R^T 1 = Q1
  * row feasibility: the 6 mixed entries of each A/B row are in 0..4 with
    sum 12 - 2 sigma_i and square-sum 22 - (squares on A u B)
  * G6 = 3C6 + 12 I - 4 J - 2 u u^T (6x6 principal block of G) is PSD of rank <= 4
Exact arithmetic via fractions (LDL^T with pivoting on a PSD test).
"""
from fractions import Fraction as F
from itertools import product, permutations
import sys

def psd_rank(M):
    """Exact PSD test + rank for a symmetric rational matrix (Gaussian elim on PSD)."""
    n = len(M)
    M = [[F(x) for x in row] for row in M]
    rank = 0
    idx = list(range(n))
    active = list(range(n))
    while active:
        # choose positive diagonal pivot
        piv = None
        for i in active:
            if M[i][i] < 0:
                return False, None
            if M[i][i] > 0 and piv is None:
                piv = i
        if piv is None:
            # all diagonals zero: PSD iff remaining block zero
            for i in active:
                for j in active:
                    if M[i][j] != 0:
                        return False, None
            break
        p = M[piv][piv]
        rest = [i for i in active if i != piv]
        for i in rest:
            f = M[i][piv] / p
            for j in rest:
                M[i][j] -= f * M[piv][j]
        active = rest
        rank += 1
    return True, rank

def mixed_feasible(s, q):
    """exist 6 ints in 0..4 with sum s and square-sum q?"""
    if s < 0: return False
    def rec(k, s, q, lo):
        if k == 0: return s == 0 and q == 0
        for x in range(lo, 5):
            if x * k > s + 0 and False: pass
            if x > s: break
            if x * x > q: break
            if rec(k - 1, s - x, q - x * x, x): return True
        return False
    return rec(6, s, q, 0)

A, B = [0, 1, 2], [3, 4, 5]
u6 = [1, 1, 1, -1, -1, -1]

def gram6(C6):
    return [[3 * C6[i][j] + (12 if i == j else 0) - 4 - 2 * u6[i] * u6[j] for j in range(6)] for i in range(6)]

def main():
    sols = []
    rng = range(5)
    for p01, p02, p12, q01, q02, q12 in product(rng, repeat=6):
        P = [[0, p01, p02], [p01, 0, p12], [p02, p12, 0]]
        Q = [[0, q01, q02], [q01, 0, q12], [q02, q12, 0]]
        rs = [sum(r) for r in P]
        cs = [sum(r) for r in Q]
        if sum(rs) != sum(cs):
            continue
        # enumerate R (3x3, entries 0..4) with row sums rs, col sums cs
        rows = []
        for i in range(3):
            rows.append([r for r in product(rng, repeat=3) if sum(r) == rs[i]])
        for r0 in rows[0]:
            for r1 in rows[1]:
                for r2 in rows[2]:
                    if any(r0[j] + r1[j] + r2[j] != cs[j] for j in range(3)):
                        continue
                    R = [list(r0), list(r1), list(r2)]
                    C6 = [[0] * 6 for _ in range(6)]
                    for i in range(3):
                        for j in range(3):
                            C6[i][j] = P[i][j]; C6[3 + i][3 + j] = Q[i][j]
                            C6[i][3 + j] = R[i][j]; C6[3 + j][i] = R[i][j]
                    ok = True
                    for i in range(6):
                        sig = sum(C6[i][j] for j in (A if i < 3 else B))
                        sq = sum(C6[i][j] ** 2 for j in range(6))
                        if not mixed_feasible(12 - 2 * sig, 22 - sq):
                            ok = False; break
                    if not ok:
                        continue
                    psd, rk = psd_rank(gram6(C6))
                    if psd and rk <= 4:
                        sols.append(C6)

    print("labelled first-six blocks surviving:", len(sols))

    # canonical form under S3 x S3 x (swap A<->B)
    def canon(C6):
        best = None
        for pa in permutations(A):
            for pb in permutations(B):
                for swap in (False, True):
                    order = (list(pb) + list(pa)) if swap else (list(pa) + list(pb))
                    M = tuple(tuple(C6[order[i]][order[j]] for j in range(6)) for i in range(6))
                    if best is None or M < best:
                        best = M
        return best

    classes = {}
    for C6 in sols:
        classes.setdefault(canon(C6), []).append(C6)
    print("classes up to S3 x S3 x swap:", len(classes))
    for k, (c, members) in enumerate(sorted(classes.items())):
        h = (c[0][1] + c[0][2] + c[1][2])
        print(f"class {k}: h={h}, labelled members={len(members)}, rank G6={psd_rank(gram6(c))[1]}")
        for row in c:
            print("   ", row)

if __name__ == '__main__':
    main()
