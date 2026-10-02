#!/usr/bin/env python3
"""Mixed vectors for the six cases in the write-up labelling (same test as mixed6.py)."""
from itertools import product
from census6 import psd_rank, gram6
from cases6 import CASES

if __name__ == '__main__':
    for k, C6 in CASES.items():
        G6 = gram6(C6)
        assert psd_rank(G6) == (True, 4)
        xs = []
        for x in product(range(5), repeat=6):
            if sum(x[:3]) != sum(x[3:]): continue
            g = [3 * xi - 4 for xi in x]
            M = [row + [g[i]] for i, row in enumerate(G6)] + [g + [8]]
            if psd_rank(M) == (True, 4): xs.append(x)
        row = C6[0]
        s, q = 12 - 2 * sum(row[:3]), 22 - sum(c * c for c in row)
        vals = sorted({x[0] for x in xs})
        feas = [y for y in product(vals, repeat=6) if sum(y) == s and sum(v * v for v in y) == q]
        print(f"case {k}: {len(xs)} mixed vectors (x_a1..a3; x_b1..b3): {xs}")
        print(f"   C(m,a1) in {vals}; row a1 needs sum {s}, square-sum {q}; feasible: {len(feas)}")
