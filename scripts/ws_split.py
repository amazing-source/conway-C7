#!/usr/bin/env python3
"""Uniform W (+) S splitting for the six cases (P = Q, R = R^T):
w_i = v_ai - v_bi, s_i = v_ai + v_bi are mutually orthogonal.
For a mixed m:  v_m.w_i = 3 d_i (d = x - y),  v_m.s_i = e_i = 3(x_i + y_i) - 8."""
import sympy as sp
from cases6 import CASES as cases

for k, C6 in cases.items():
    P = sp.Matrix(3, 3, lambda i, j: C6[i][j])
    Q = sp.Matrix(3, 3, lambda i, j: C6[3 + i][3 + j])
    R = sp.Matrix(3, 3, lambda i, j: C6[i][3 + j])
    assert P == Q and R == R.T
    I, J = sp.eye(3), sp.ones(3, 3)
    Gw = 2 * (3 * P - 3 * R + 12 * I - 4 * J)
    Gs = 2 * (3 * P + 3 * R + 12 * I - 8 * J)
    print(f"case {k}: P={P.tolist()} R={R.tolist()}")
    print(f"   Gw={Gw.tolist()} rank {Gw.rank()}  ker {[list(v.T) for v in Gw.nullspace()]}")
    print(f"   Gs={Gs.tolist()} rank {Gs.rank()}  ker {[list(v.T) for v in Gs.nullspace()]}")
