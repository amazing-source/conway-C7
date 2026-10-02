"""Sanity check (not part of the proof). Audit 3: mixed-orbit attachments in the six configurations, by brute force with exact
PSD/rank tests on the 7x7 Gram block, then the row-a1 contradiction."""
from itertools import product
import sys
sys.path.insert(0, '.')
from residuals import psd_rank

T111 = [[0,1,1],[1,0,1],[1,1,0]]; T112 = [[0,1,1],[1,0,2],[1,2,0]]
T113 = [[0,1,1],[1,0,3],[1,3,0]]; T122 = [[0,1,2],[1,0,2],[2,2,0]]
CASES = {1: (T111, [[2,0,0],[0,2,0],[0,0,2]]), 2: (T111, [[2,0,0],[0,1,1],[0,1,1]]),
         3: (T111, T111), 4: (T112, T112), 5: (T113, [[0,1,1],[1,1,2],[1,2,1]]),
         6: (T122, [[0,1,2],[1,2,0],[2,0,2]])}
PAPER = {1: {(3,1,0,3,0,1),(3,0,1,3,1,0)}, 2: {(1,3,0,0,2,2),(1,0,3,0,2,2),(0,2,2,1,3,0),(0,2,2,1,0,3)},
         3: {(0,2,2,0,2,2)}, 4: {(0,2,2,0,2,2),(2,0,0,2,0,0),(2,2,2,2,2,2)},
         5: {(0,2,2,0,2,2),(2,2,0,2,0,2),(2,0,2,2,2,0)},
         6: {(0,2,0,0,2,0),(1,0,0,1,0,0),(1,0,2,1,0,2),(1,3,0,1,3,0)}}  # (1,3,2;1,3,2) violates (6)
U7 = [1,1,1,-1,-1,-1,0]

def perm_closure(S):
    """close under common permutations of indices that fix the configuration? -- not used; paper
    lists are 'up to a common permutation' only in case 1 and 3; we compare value sets of x_1."""
    return S

for k,(P,R) in CASES.items():
    B = [[0]*7 for _ in range(7)]
    for i in range(3):
        for j in range(3):
            B[i][j] = P[i][j]; B[3+i][3+j] = P[i][j]; B[i][3+j] = R[i][j]; B[3+j][i] = R[i][j]
    sols = []
    for xy in product(range(5), repeat=6):
        x, y = xy[:3], xy[3:]
        if sum(x) != sum(y): continue
        if sum(xy) > 12 or sum(t*t for t in xy) > 24: continue
        for i in range(3):
            B[6][i] = B[i][6] = x[i]; B[6][3+i] = B[3+i][6] = y[i]
        G = [[(12 if i == j else 0) + 3*B[i][j] - 4 - 2*U7[i]*U7[j] for j in range(7)] for i in range(7)]
        ok, rk = psd_rank(G)
        if ok and rk <= 4: sols.append(xy)
    S = set(sols)
    x1vals = sorted(set(s[0] for s in S))
    print(f"case {k}: {len(S)} mixed vectors; x1 values {x1vals}")
    print("   ", sorted(S))
    # paper's list: in cases 1 and 3 it is up to a common permutation of indices
    if k in (1, 3):
        from itertools import permutations
        cl = set()
        for s in PAPER[k]:
            for p in permutations(range(3)):
                cl.add(tuple(s[p[i]] for i in range(3)) + tuple(s[3+p[i]] for i in range(3)))
        print("    paper list (closed under common perms) equal:", cl == S)
    else:
        print("    paper list equal:", PAPER[k] == S)
    # row a1 contradiction: entries over the six mixed columns take values in x1vals,
    # with sum 12-2*sigma and square-sum 22 - (block squares)
    row = [B[0][j] for j in range(6)]
    tot, sq = 12 - sum(row), 22 - sum(t*t for t in row)
    feas = [c for c in product(x1vals, repeat=6) if sum(c) == tot and sum(t*t for t in c) == sq]
    print(f"    row a1 needs sum {tot}, square-sum {sq}: completions {len(feas)}")
