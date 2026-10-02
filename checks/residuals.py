"""Independent exact audit of the finite steps of the order-7 proof.
Written from scratch (does not reuse the repo's scripts). Exact rational arithmetic only."""
from fractions import Fraction as F
from itertools import product, permutations
import math

def gram_block(C, idx, u):
    # G = 3C + 12I - 4J - 2uu^T restricted to idx
    return [[3*C[i][j] + (12 if i == j else 0) - 4 - 2*u[i]*u[j] for j in idx] for i in idx]

def psd_rank(M):
    """Exact: return (is_psd, rank) for a symmetric rational matrix via symmetric Gaussian elimination."""
    n = len(M); A = [[F(x) for x in row] for row in M]; rank = 0
    active = list(range(n))
    while active:
        # pick a positive pivot on the diagonal
        piv = None
        for i in active:
            if A[i][i] < 0: return (False, None)
            if A[i][i] > 0 and piv is None: piv = i
        if piv is None:
            # all remaining diagonal zero: PSD iff remaining block is zero
            for i in active:
                for j in active:
                    if A[i][j] != 0: return (False, None)
            return (True, rank)
        rank += 1
        p = A[piv][piv]
        rest = [i for i in active if i != piv]
        for i in rest:
            for j in rest:
                A[i][j] -= A[i][piv]*A[piv][j]/p
        active = rest
    return (True, rank)

# ---------- 1. alpha tables ----------
T = {'111': [[0,1,1],[1,0,1],[1,1,0]], '112': [[0,1,1],[1,0,2],[1,2,0]],
     '113': [[0,1,1],[1,0,3],[1,3,0]], '122': [[0,1,2],[1,0,2],[2,2,0]]}

def inv3(M):
    a,b,c = M[0]; d,e,f = M[1]; g,h,i = M[2]
    det = a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)
    adj = [[e*i-f*h, c*h-b*i, b*f-c*e],[f*g-d*i, a*i-c*g, c*d-a*f],[d*h-e*g, b*g-a*h, a*e-b*d]]
    return det, [[F(adj[r][s], det) for s in range(3)] for r in range(3)]

def alpha(Pname, c):
    P = T[Pname]
    GA = [[6 if i == j else 3*P[i][j]-6 for j in range(3)] for i in range(3)]
    det, Gi = inv3(GA)
    X = [3*ci-2 for ci in c]
    q = sum(X[i]*Gi[i][j]*X[j] for i in range(3) for j in range(3))
    return 12*(6 - q), det

print("== determinants of G_A")
for k in ['112','113','122']:
    print(k, inv3([[6 if i == j else 3*T[k][i][j]-6 for j in range(3)] for i in range(3)])[0])

print("== alpha tables (all columns with the given sum; '-' marks z^2<0)")
tables = {}
for k, sums in [('112',[2,3]),('113',[2,3,4]),('122',[2,3,4])]:
    for s in sums:
        cols = [c for c in product(range(5), repeat=3) if sum(c) == s]
        vals = {}
        for c in cols:
            a, _ = alpha(k, c)
            assert a.denominator == 1, (k, c, a)
            vals[c] = int(a)
        tables[(k,s)] = vals
        pos = sorted([(v,c) for c,v in vals.items() if v >= 0], reverse=True)
        neg = sorted([(v,c) for c,v in vals.items() if v < 0], reverse=True)
        print(k, s, 'nonneg:', pos)
        print('      neg:', neg)

# ---------- 2. square-root triples ----------
def issq(n): return n >= 0 and math.isqrt(n)**2 == n

def triples(k, sums):
    """all (alpha_b1, alpha_b2, alpha_b3) compatible with z sum zero"""
    res = []
    lists = [sorted(set(v for v in tables[(k,s)].values() if v >= 0)) for s in sums]
    for a in product(*lists):
        # exists signs with sum sqrt = 0 : largest sqrt = sum of other two
        r = sorted(a)
        if r[0]*r[1] >= 0 and issq(r[0]*r[1]):
            # sqrt(r2) == sqrt(r0)+sqrt(r1)  <=> r2 = r0 + r1 + 2 sqrt(r0 r1)
            if r[2] == r[0] + r[1] + 2*math.isqrt(r[0]*r[1]): res.append(a)
    return res

print("== square-root triples")
for (k, sums) in [('112',[2,3,3]), ('113',[2,4,4]), ('113',[3,3,4]), ('122',[3,3,4]), ('122',[2,4,4])]:
    print(k, sums, triples(k, sums))
print("all square products among T122 sum-3/sum-4 values (different columns):")
v3 = sorted(set(v for v in tables[('122',3)].values() if v >= 0)); v4 = sorted(set(v for v in tables[('122',4)].values() if v >= 0))
print(' b1,b2 pairs:', [(a,b) for a in v3 for b in v3 if a <= b and issq(a*b)])
print(' bj,b3 pairs:', [(a,b) for a in v3 for b in v4 if issq(a*b)])
