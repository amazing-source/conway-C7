#!/usr/bin/env python3
"""Generate the Lean case analysis for the core matrix lemma (ordre7/lean/Ordre7/Gen/*.lean).

Every leaf certificate is computed here with exact arithmetic and re-checked by Lean.
Indices: 0,1,2 = a1,a2,a3 (u=1); 3,4,5 = b1,b2,b3 (u=-1); 6..11 mixed (u=0).
"""
import itertools
import sympy as sp
from fractions import Fraction as F
from math import gcd

U = [1, 1, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0]
AB = list(range(6))


def Gent(i, j, c):
    """G entry from C entry c (c = C_ij, with C_ii = 0)."""
    return 3 * c + (12 if i == j else 0) - 4 - 2 * U[i] * U[j]


def block_from(P, Q, R):
    C6 = [[0] * 6 for _ in range(6)]
    for i in range(3):
        for j in range(3):
            C6[i][j] = P[i][j]; C6[3 + i][3 + j] = Q[i][j]
            C6[i][3 + j] = R[i][j]; C6[3 + j][i] = R[i][j]
    return C6


def G6_of(C6):
    return [[Gent(i, j, C6[i][j]) for j in range(6)] for i in range(6)]


def choose_basis(G6):
    """4-subset S of 0..5 with nonzero det; returns (S, Adj, D) with Adj*G_S = D*I, D>0, gcd-reduced."""
    best = None
    for S in itertools.combinations(range(6), 4):
        M = sp.Matrix([[G6[i][j] for j in S] for i in S])
        d = M.det()
        if d != 0:
            adj = M.adjugate()
            if d < 0:
                adj = -adj; d = -d
            g = int(d)
            for x in adj:
                g = gcd(g, int(x))
            adj = adj / g; d = d // g
            cand = (list(S), [[int(adj[r, c]) for c in range(4)] for r in range(4)], int(d))
            score = max(abs(x) for row in cand[1] for x in row) + cand[2]
            if best is None or score < best[0]:
                best = (score, cand)
    return best[1]


def mixed_system(G6, S, Adj, D):
    """Return (linear equations as coefficient rows over x0..x5 + const, quadratic poly) for a mixed m.
    x_j = C_{m j}, g_j = 3 x_j - 4."""
    xs = sp.symbols('x0:6', integer=True)
    g = [3 * xs[j] - 4 for j in range(6)]
    Jrest = [j for j in range(6) if j not in S]
    lin = []
    for j in Jrest:
        rhs = sum(sum(g[S[s]] * Adj[s][t] for s in range(4)) * G6[S[t]][j] for t in range(4))
        lin.append(sp.expand(D * g[j] - rhs))
    lin.append(sp.expand(xs[0] + xs[1] + xs[2] - xs[3] - xs[4] - xs[5]))
    quad = sp.expand(D * 8 - sum(sum(g[S[s]] * Adj[s][t] for s in range(4)) * g[S[t]] for t in range(4)))
    return xs, Jrest, lin, quad


def solve_mixed(G6, S, Adj, D):
    xs, Jrest, lin, quad = mixed_system(G6, S, Adj, D)
    sols = []
    for x in itertools.product(range(5), repeat=6):
        sub = dict(zip(xs, x))
        if all(e.subs(sub) == 0 for e in lin) and quad.subs(sub) == 0:
            sols.append(x)
    # choose 3 free variables such that the 3 linear equations determine the other 3
    A = sp.Matrix([[sp.Poly(e, *xs).coeff_monomial(xs[j]) for j in range(6)] for e in lin])
    rk = A.rank()
    free = None
    for dep in itertools.combinations(range(6), rk):
        if A.extract(list(range(A.rows)), list(dep)).rank() == rk:
            free = [j for j in range(6) if j not in dep]
            dep = list(dep)
            break
    return sols, free, dep, Jrest


def row_contradiction(C6, sols):
    """Find a row r in A u B whose mixed part is infeasible given allowed values."""
    for r in range(6):
        vals = sorted({x[r] for x in sols})
        s = 12 - sum(C6[r])
        q = 22 - sum(c * c for c in C6[r])
        feas = any(sum(y) == s and sum(v * v for v in y) == q for y in itertools.product(vals, repeat=6))
        if not feas:
            return r, vals, s, q
    return None


def lean_mat4(M):
    return "!![" + "; ".join(", ".join(str(x) for x in row) for row in M) + "]"


def block_hyps(C6):
    """Hypothesis names/statements for the 15 upper entries of the block."""
    hs = []
    for i in range(6):
        for j in range(i + 1, 6):
            hs.append((f"h{i}{j}", i, j, C6[i][j]))
    return hs


def gen_block(name, C6):
    G6 = G6_of(C6)
    S, Adj, D = choose_basis(G6)
    sols, free, dep, Jrest = solve_mixed(G6, S, Adj, D)
    rc = row_contradiction(C6, sols)
    assert rc is not None, (name, C6)
    r, vals, s, q = rc
    hs = block_hyps(C6)
    L = []
    L.append(f"/-- Block `{name}`: mixed vectors {sols}; row {r} takes values in {vals} "
             f"but needs sum {s}, square-sum {q}. -/")
    L.append(f"theorem {name} {{C : Matrix (Fin 12) (Fin 12) ℤ}} (hC : IsOrbitMatrix C)")
    L.append("    " + " ".join(f"({h} : C {i} {j} = {v})" for h, i, j, v in hs) + " : False := by")
    for h, i, j, v in hs:
        L.append(f"  have {h}' : C {j} {i} = {v} := by rw [hC.symm]; exact {h}")
    simp_block = ", ".join([h for h, *_ in hs] + [h + "'" for h, *_ in hs])
    Sl = "![" + ", ".join(str(x) for x in S) + "]"
    GSm = [[G6[a][b] for b in S] for a in S]
    L.append(f"  have hGS : GS {Sl} C = {lean_mat4(GSm)} := by")
    L.append(f"    ext s t; fin_cases s <;> fin_cases t <;> simp [GS, G_apply, hC.diag, {simp_block}]")
    L.append(f"  have hAdj : ({lean_mat4(Adj)} : Matrix (Fin 4) (Fin 4) ℤ) * GS {Sl} C = ({D} : ℤ) • 1 := by")
    L.append(f"    rw [hGS]; decide")
    L.append(f"  have hAdjT : ({lean_mat4(Adj)} : Matrix (Fin 4) (Fin 4) ℤ)ᵀ = {lean_mat4(Adj)} := by decide")
    goal = " ∨ ".join(f"C m {r} = {v}" for v in vals)
    L.append(f"  have key : ∀ m : Fin 12, 6 ≤ m.val → {goal} := by")
    L.append(f"    intro m hm")
    L.append(f"    have hu : u m = 0 := u_of_ge6 m hm")
    for k in range(6):
        L.append(f"    have hm{k} : m ≠ {k} := ne_of_ge6 m hm {k} (by decide)")
        L.append(f"    have s{k} : C {k} m = C m {k} := hC.symm {k} m")
    for idx, j in enumerate(Jrest):
        L.append(f"    have f{idx} := hC.factor_apply {Sl} _ _ (by norm_num) hAdjT hAdj m {j}")
    L.append(f"    have fq := hC.factor_apply {Sl} _ _ (by norm_num) hAdjT hAdj m m")
    L.append(f"    have hus := hC.usum_expand m")
    L.append(f"    simp [Fin.sum_univ_four, G_apply, hC.diag, hu, "
             f"{', '.join(f'hm{k}' for k in range(6))}, {', '.join(f's{k}' for k in range(6))}, "
             f"{simp_block}] at f0 f1 fq")
    for k in range(6):
        L.append(f"    have l{k} := hC.nonneg m {k}")
        L.append(f"    have g{k} := hC.le4 m {k}")
    for k in range(6):
        L.append(f"    generalize C m {k} = x{k} at *")
    tac = " <;> ".join(f"interval_cases x{k}" for k in free)
    dep_tac = " <;> ".join(f"(try omega) <;> interval_cases x{k}" for k in dep)
    L.append(f"    {tac} <;> {dep_tac} <;> omega")
    # final row contradiction
    L.append(f"  have hrow := hC.row_expand {r}")
    L.append(f"  have hsq := hC.sq_expand {r}")
    for m in range(6, 12):
        L.append(f"  have k{m} := key {m} (by decide)")
        L.append(f"  have t{m} : C {r} {m} = C {m} {r} := hC.symm {r} {m}")
    L.append(f"  simp only [hC.diag, {', '.join(f't{m}' for m in range(6, 12))}, {simp_block}, "
             f"u0, u1, u2, u3, u4, u5] at hrow hsq")
    for m in range(6, 12):
        L.append(f"  generalize C {m} {r} = c{m} at *")
    L.append("  " + " <;> ".join(f"rcases k{m} with " + " | ".join(["rfl"] * len(vals)) for m in range(6, 12))
             + " <;> omega")
    return "\n".join(L), dict(S=S, Adj=Adj, D=D, sols=sols, free=free, dep=dep, row=r, vals=vals)


HEADER = """import Ordre7.Basic

/-! Generated by `ordre7/scripts/gen_lean.py` -- do not edit by hand. -/

open Matrix Finset

namespace Ordre7

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
"""

# ---------------------------------------------------------------------------
# improved block generator (dependent variables substituted when integral)

PAIRS = [(i, j) for i in range(6) for j in range(i + 1, 6)]
HNAMES = [f"h{i}{j}" for i, j in PAIRS]


def lean_lin(expr, xs):
    """Format an integral linear sympy expression in xs as Lean."""
    poly = sp.Poly(expr, *xs)
    parts = [f"({int(poly.coeff_monomial(1))} : ℤ)"]
    for k, x in enumerate(xs):
        c = poly.coeff_monomial(x)
        if c != 0:
            parts.append(f"({int(c)}) * x{k}")
    return " + ".join(parts)


def sym_facts(C6, names=None):
    """`have hji' : C j i = v` lines and the simp list of all 30 block facts."""
    L = []
    for (i, j), h in zip(PAIRS, HNAMES):
        L.append(f"  have {h}' : C {j} {i} = {C6[i][j]} := by rw [hC.symm]; exact {h}")
    simp_block = ", ".join(HNAMES + [h + "'" for h in HNAMES])
    return L, simp_block


def gen_block2(name, C6):
    G6 = G6_of(C6)
    S, Adj, D = choose_basis(G6)
    xs, Jrest, lin, quad = mixed_system(G6, S, Adj, D)
    sols, free, dep, _ = solve_mixed(G6, S, Adj, D)
    rc = row_contradiction(C6, sols)
    assert rc is not None, (name, C6)
    r, vals, ssum, qsum = rc
    sol = sp.solve(lin, [xs[d] for d in dep], dict=True)
    assert len(sol) == 1
    sol = sol[0]
    subst = {}
    for d in dep:
        e = sp.expand(sol[xs[d]])
        poly = sp.Poly(e, *xs)
        if all(c.is_integer for c in poly.coeffs()):
            subst[d] = e
    L = []
    L.append(f"/-- Block `{name}`: the mixed vectors are {sols}; row {r} would need six values in "
             f"{vals} with sum {ssum} and square-sum {qsum}. -/")
    L.append(f"theorem {name} {{C : Matrix (Fin 12) (Fin 12) ℤ}} (hC : IsOrbitMatrix C)")
    hyp = " ".join(f"({h} : C {i} {j} = {C6[i][j]})" for (i, j), h in zip(PAIRS, HNAMES))
    L.append(f"    {hyp} :")
    L.append("    False := by")
    sf, simp_block = sym_facts(C6)
    L += sf
    Sl = "![" + ", ".join(str(x) for x in S) + "]"
    GSm = [[G6[a][b] for b in S] for a in S]
    L.append(f"  have hGS : GS {Sl} C = {lean_mat4(GSm)} := by")
    L.append(f"    ext s t; fin_cases s <;> fin_cases t <;> simp [GS, G_apply, hC.diag, {simp_block}]")
    L.append(f"  have hAdj : ({lean_mat4(Adj)} : Matrix (Fin 4) (Fin 4) ℤ) * GS {Sl} C = ({D} : ℤ) • 1 := by")
    L.append(f"    rw [hGS]; decide")
    L.append(f"  have hAdjT : ({lean_mat4(Adj)} : Matrix (Fin 4) (Fin 4) ℤ)ᵀ = {lean_mat4(Adj)} := by decide")
    goal = " ∨ ".join(f"C m {r} = {v}" for v in vals)
    L.append(f"  have key : ∀ m : Fin 12, 6 ≤ m.val → {goal} := by")
    L.append(f"    intro m hm")
    L.append(f"    have hu : u m = 0 := u_of_ge6 m hm")
    for k in range(6):
        L.append(f"    have hm{k} : m ≠ {k} := ne_of_ge6 m hm {k} (by decide)")
        L.append(f"    have s{k} : C {k} m = C m {k} := hC.symm {k} m")
    L.append(f"    have f0 := hC.factor_apply {Sl} _ _ (by norm_num) hAdjT hAdj m {Jrest[0]}")
    L.append(f"    have f1 := hC.factor_apply {Sl} _ _ (by norm_num) hAdjT hAdj m {Jrest[1]}")
    L.append(f"    have fq := hC.factor_apply {Sl} _ _ (by norm_num) hAdjT hAdj m m")
    L.append(f"    have hus := hC.usum_expand m")
    L.append(f"    simp [Fin.sum_univ_four, G_apply, hC.diag, hu, "
             f"{', '.join(f'hm{k}' for k in range(6))}, {', '.join(f's{k}' for k in range(6))}, "
             f"{simp_block}] at f0 f1 fq")
    for k in range(6):
        L.append(f"    have l{k} := hC.nonneg m {k}")
        L.append(f"    have g{k} := hC.le4 m {k}")
    for k in range(6):
        L.append(f"    generalize C m {k} = x{k} at *")
    for d, e in subst.items():
        L.append(f"    have e{d} : x{d} = {lean_lin(e, xs)} := by omega")
        L.append(f"    subst e{d}")
    rest = [d for d in dep if d not in subst]
    steps = [f"interval_cases x{k}" for k in free] + [f"interval_cases x{k}" for k in rest]
    L.append("    " + " <;> (try omega) <;> ".join(steps) + " <;> omega")
    L.append(f"  have hrow := hC.row_expand {r}")
    L.append(f"  have hsq := hC.sq_expand {r}")
    for m in range(6, 12):
        L.append(f"  have k{m} := key {m} (by decide)")
        L.append(f"  have t{m} : C {r} {m} = C {m} {r} := hC.symm {r} {m}")
    L.append(f"  simp only [hC.diag, {', '.join(f't{m}' for m in range(6, 12))}, {simp_block}, "
             f"u0, u1, u2, u3, u4, u5] at hrow hsq")
    for m in range(6, 12):
        L.append(f"  generalize C {m} {r} = c{m} at *")
    L.append("  " + " <;> ".join(f"rcases k{m} with " + " | ".join(["rfl"] * len(vals)) for m in range(6, 12))
             + " <;> omega")
    return "\n".join(L)


# ---------------------------------------------------------------------------
# census

TT = {'111': [[0, 1, 1], [1, 0, 1], [1, 1, 0]], '112': [[0, 1, 1], [1, 0, 2], [1, 2, 0]],
      '113': [[0, 1, 1], [1, 0, 3], [1, 3, 0]], '122': [[0, 1, 2], [1, 0, 2], [2, 2, 0]]}
PAIRS_PQ = [('111', '111'), ('112', '112'), ('113', '113'), ('113', '122'), ('122', '113'), ('122', '122')]


def valid_block(C6):
    G = sp.Matrix(G6_of(C6))
    S = [0, 1, 2, 3]
    GS = G.extract(S, S)
    if GS.det() == 0:
        return None
    Gc = G.extract(list(range(6)), S)
    return (Gc * GS.inv() * Gc.T - G) == sp.zeros(6, 6)


def col_opts(total):
    return [c for c in itertools.product(range(5), repeat=3) if sum(c) == total]


def conj3(col, b):
    return " ∧ ".join(f"C {a} {b} = {col[a]}" for a in range(3))


def disj_cols(cols, b):
    return " ∨ ".join(f"({conj3(c, b)})" for c in cols)


def pat3(n):
    return " | ".join(["⟨" + ", ".join(f"h{a}{n}" for a in range(3)) + "⟩"] * 1)


def rc_pattern(b, k):
    one = "⟨" + ", ".join(f"h{a}{b}" for a in range(3)) + "⟩"
    return " | ".join([one] * k)


def gen_census(pn, qn, blocks):
    P, Q = TT[pn], TT[qn]
    sA = [sum(r) for r in P]; sB = [sum(r) for r in Q]
    name = f"census_{pn}_{qn}"
    pq_h = [("h01", 0, 1, P[0][1]), ("h02", 0, 2, P[0][2]), ("h12", 1, 2, P[1][2]),
            ("h34", 3, 4, Q[0][1]), ("h35", 3, 5, Q[0][2]), ("h45", 4, 5, Q[1][2])]
    L = []
    L.append(f"theorem {name} {{C : Matrix (Fin 12) (Fin 12) ℤ}} (hC : IsOrbitMatrix C)")
    L.append("    " + " ".join(f"({h} : C {i} {j} = {v})" for h, i, j, v in pq_h) + " : False := by")
    for h, i, j, v in pq_h:
        L.append(f"  have {h}' : C {j} {i} = {v} := by rw [hC.symm]; exact {h}")
    for a in range(3):
        for b in range(3, 6):
            L.append(f"  have s{b}{a} : C {b} {a} = C {a} {b} := hC.symm {b} {a}")
    for a in range(3):
        for b in range(3, 6):
            L.append(f"  have l{a}{b} := hC.nonneg {a} {b}")
            L.append(f"  have g{a}{b} := hC.le4 {a} {b}")
    for k in range(6):
        L.append(f"  have m{k} := hC.margin {k}")
    pq_simp = ", ".join([h for h, *_ in pq_h] + [h + "'" for h, *_ in pq_h])
    rsym = ", ".join(f"s{b}{a}" for a in range(3) for b in range(3, 6))
    L.append(f"  simp only [hC.diag, {pq_simp}, {rsym}] at m0 m1 m2 m3 m4 m5")
    count = 0
    if pn == '111':
        L.append(f"  have kA := hC.comb_ker ![0, 1, 2] ![1, 1, 1] (by rw [hC.quadA]; omega)")
        L.append(f"  have kB := hC.comb_ker ![3, 4, 5] ![1, 1, 1] (by rw [hC.quadB]; omega)")
        L.append(f"  have k3 := kA 3")
        L.append(f"  have k4 := kA 4")
        L.append(f"  have k5 := kA 5")
        L.append(f"  have k0 := kB 0")
        L.append(f"  have k1 := kB 1")
        L.append(f"  have k2 := kB 2")
        L.append(f"  simp [Fin.sum_univ_three, G_apply, {rsym}] at k3 k4 k5 k0 k1 k2")
        cs = {b: col_opts(2) for b in (3, 4, 5)}
        L.append(f"  have c3 : {disj_cols(cs[3], 3)} := by omega")
        L.append(f"  have c4 : {disj_cols(cs[4], 4)} := by omega")
        L.append(f"  have c5 : {disj_cols(cs[5], 5)} := by omega")
        L.append(f"  rcases c3 with {rc_pattern(3, len(cs[3]))}")
        for c3 in cs[3]:
            L.append(f"  · rcases c4 with {rc_pattern(4, len(cs[4]))}")
            for c4 in cs[4]:
                L.append(f"    · rcases c5 with {rc_pattern(5, len(cs[5]))}")
                for c5 in cs[5]:
                    R = [[c3[a], c4[a], c5[a]] for a in range(3)]
                    if any(sum(R[a]) != 2 for a in range(3)):
                        L.append(f"      · omega")
                    else:
                        C6 = block_from(P, Q, R)
                        bn = blocks.setdefault(tuple(map(tuple, C6)), f"block_{len(blocks)}")
                        L.append(f"      · exact {bn} hC " + " ".join(HNAMES))
                    count += 1
        return "\n".join(L), count
    cols = {b: col_opts(sB[b - 3]) for b in (3, 4, 5)}
    L.append(f"  have c3 : {disj_cols(cols[3], 3)} := by omega")
    L.append(f"  rcases c3 with {rc_pattern(3, len(cols[3]))}")
    for c3 in cols[3]:
        R0 = [[c3[a], 0, 0] for a in range(3)]
        C6 = block_from(P, Q, R0)
        G6 = G6_of(C6)
        MA = sp.Matrix([[G6[i][j] for j in range(4)] for i in range(4)])
        d = MA.det()
        fact = f"{pq_simp}, h03, h13, h23, {rsym}"
        if d <= 0:
            assert d < 0
            GA = sp.Matrix([[G6[i][j] for j in range(3)] for i in range(3)])
            X = sp.Matrix([G6[a][3] for a in range(3)])
            y = list(GA.adjugate() * X) + [-GA.det()]
            g = 0
            for t in y: g = gcd(g, int(t))
            y = [int(t) // g for t in y]
            yv = sp.Matrix(y)
            assert (yv.T * MA * yv)[0] < 0
            L.append(f"  · have q := hC.comb_nonneg ![0, 1, 2, 3] ![{', '.join(map(str, y))}]")
            L.append(f"    simp [Fin.sum_univ_four, G_apply, hC.diag, {fact}] at q <;> omega")
            count += 1
            continue
        S, Adj, D = [0, 1, 2, 3], None, None
        adj = MA.adjugate(); D = int(d)
        g = D
        for t in adj: g = gcd(g, int(t))
        Adj = [[int(adj[r, c]) // g for c in range(4)] for r in range(4)]; D //= g
        GSm = [[G6[a][b] for b in range(4)] for a in range(4)]
        L.append(f"  · have hGS : GS ![0, 1, 2, 3] C = {lean_mat4(GSm)} := by")
        L.append(f"      ext s t; fin_cases s <;> fin_cases t <;> simp [GS, G_apply, hC.diag, {fact}]")
        L.append(f"    have hAdj : ({lean_mat4(Adj)} : Matrix (Fin 4) (Fin 4) ℤ) * GS ![0, 1, 2, 3] C = "
                 f"({D} : ℤ) • 1 := by")
        L.append(f"      rw [hGS]; decide")
        L.append(f"    have hAdjT : ({lean_mat4(Adj)} : Matrix (Fin 4) (Fin 4) ℤ)ᵀ = {lean_mat4(Adj)} := by decide")
        for (i, j) in [(4, 4), (4, 5), (5, 5)]:
            L.append(f"    have f{i}{j} := hC.factor_apply ![0, 1, 2, 3] _ _ (by norm_num) hAdjT hAdj {i} {j}")
        L.append(f"    simp [Fin.sum_univ_four, G_apply, hC.diag, {fact}] at f44 f45 f55")
        L.append(f"    have c4 : {disj_cols(cols[4], 4)} := by omega")
        L.append(f"    have c5 : {disj_cols(cols[5], 5)} := by omega")
        L.append(f"    rcases c4 with {rc_pattern(4, len(cols[4]))}")
        for c4 in cols[4]:
            L.append(f"    · rcases c5 with {rc_pattern(5, len(cols[5]))}")
            for c5 in cols[5]:
                R = [[c3[a], c4[a], c5[a]] for a in range(3)]
                C6 = block_from(P, Q, R)
                ok = all(sum(R[a]) == sA[a] for a in range(3)) and valid_block(C6)
                if ok:
                    bn = blocks.setdefault(tuple(map(tuple, C6)), f"block_{len(blocks)}")
                    L.append(f"      · exact {bn} hC " + " ".join(HNAMES))
                else:
                    L.append(f"      · simp only [h04, h14, h24, h05, h15, h25] at f44 f45 f55 m0 m1 m2 <;> omega")
                count += 1
    return "\n".join(L), count


def main():
    import os
    out = os.path.join(os.path.dirname(__file__), '..', 'lean', 'Ordre7', 'Gen')
    os.makedirs(out, exist_ok=True)
    blocks = {}
    census_code = []
    total = 0
    for pn, qn in PAIRS_PQ:
        code, cnt = gen_census(pn, qn, blocks)
        census_code.append(code)
        total += cnt
        print(f"census {pn}/{qn}: {cnt} leaves")
    print(f"{len(blocks)} distinct blocks, {total} census leaves")
    bitems = sorted(blocks.items(), key=lambda kv: int(kv[1].split('_')[1]))
    nb = 4
    chunks = [bitems[k::nb] for k in range(nb)]
    for f in os.listdir(out):
        if f.endswith('.lean'):
            os.remove(os.path.join(out, f))
    for k, ch in enumerate(chunks):
        bcode = [gen_block2(bn, [list(r) for r in C6]) for C6, bn in ch]
        with open(os.path.join(out, f'Blocks{k}.lean'), 'w') as f:
            f.write(HEADER.replace("import Ordre7.Basic", "import Ordre7.Setup") + "\n" +
                    "\n\n".join(bcode) + "\n\nend Ordre7\n")
    imp = "\n".join(f"import Ordre7.Gen.Blocks{k}" for k in range(nb))
    for (pn, qn), code in zip(PAIRS_PQ, census_code):
        with open(os.path.join(out, f'Census_{pn}_{qn}.lean'), 'w') as f:
            f.write(HEADER.replace("import Ordre7.Basic", imp) + "\n" + code + "\n\nend Ordre7\n")

if __name__ == '__main__':
    main()
