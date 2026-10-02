"""Audit 2: census of the 6x6 LL/RR block and of the mixed rows, by brute force with exact
PSD/rank tests (no use of the paper's lemmas except zero diagonal, row identities and rank 4)."""
from fractions import Fraction as F
from itertools import product, permutations
import sys
sys.path.insert(0, '.')
from residuals import psd_rank

U = [1,1,1,-1,-1,-1]

def gram_entry(ci, cj, cij, ui, uj, same):
    return (3*cij + 12 - 4 - 2*ui*uj) if same else (3*cij - 4 - 2*ui*uj)

def block_gram(B):
    return [[(12 if i == j else 0) + 3*B[i][j] - 4 - 2*U[i]*U[j] for j in range(6)] for i in range(6)]

def row_ok(B, i):
    s = sum(B[i]); q = sum(x*x for x in B[i])
    S = 12 - s; Qr = 22 - q   # remaining 6 mixed entries: sum S, square-sum Qr
    if S < 0 or Qr < 0: return False
    if Qr < S: return False            # integers >=0: x^2 >= x
    if 6*Qr < S*S: return False        # Cauchy
    if Qr > 4*S: return False          # entries <= 4
    return True

def mats_with_margins(rs, cs):
    """3x3 nonneg integer matrices with row sums rs and column sums cs."""
    out = []
    for r0 in product(range(5), repeat=3):
        if sum(r0) != rs[0]: continue
        for r1 in product(range(5), repeat=3):
            if sum(r1) != rs[1]: continue
            r2 = tuple(cs[j]-r0[j]-r1[j] for j in range(3))
            if min(r2) < 0 or sum(r2) != rs[2]: continue
            out.append((r0, r1, r2))
    return out

def canon(B):
    """canonical form under: permutations of A, of B, and swapping A<->B."""
    best = None
    for swap in (False, True):
        base = [3,4,5,0,1,2] if swap else [0,1,2,3,4,5]
        for pa in permutations(range(3)):
            for pb in permutations(range(3)):
                order = [base[pa[0]], base[pa[1]], base[pa[2]], base[3+pb[0]], base[3+pb[1]], base[3+pb[2]]]
                key = tuple(B[order[i]][order[j]] for i in range(6) for j in range(6))
                if best is None or key < best: best = key
    return best

classes = {}
count = 0
for p01, p02, p12 in product(range(5), repeat=3):
    P = [[0,p01,p02],[p01,0,p12],[p02,p12,0]]
    rsP = [sum(r) for r in P]
    for q01, q02, q12 in product(range(5), repeat=3):
        Q = [[0,q01,q02],[q01,0,q12],[q02,q12,0]]
        rsQ = [sum(r) for r in Q]
        if sum(rsP) != sum(rsQ): continue
        for R in mats_with_margins(rsP, rsQ):
            B = [[0]*6 for _ in range(6)]
            for i in range(3):
                for j in range(3):
                    B[i][j] = P[i][j]; B[3+i][3+j] = Q[i][j]
                    B[i][3+j] = R[i][j]; B[3+j][i] = R[i][j]
            if not all(row_ok(B, i) for i in range(6)): continue
            ok, rk = psd_rank(block_gram(B))
            if not ok or rk > 4: continue
            count += 1
            c = canon(B)
            classes.setdefault(c, []).append(B)

print("labelled 6x6 blocks passing:", count, " classes:", len(classes))
for c in sorted(classes):
    B = [list(c[6*i:6*i+6]) for i in range(6)]
    h = (B[0][1]+B[0][2]+B[1][2])
    print("h =", h, " P =", [B[0][1],B[0][2],B[1][2]], " Q =", [B[3][4],B[3][5],B[4][5]],
          " R =", [B[i][3:6] for i in range(3)], " #labelled:", len(classes[c]))
