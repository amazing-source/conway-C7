#!/usr/bin/env python3
"""Generator for the case analysis of the matrix core (Lean files Conway7/Gen/*.lean).

Everything emitted here is re-checked by Lean: the certificates (S, Adj, D) are verified by `decide`,
the finite searches are `decide +kernel` lemmas, and the glue uses only `factor_apply` (rank 4),
`comb_nonneg`/`comb_ker` (positivity) and the row identities. Nothing here is trusted.

Usage: python gen_core.py   (writes ../Conway7/Gen/*.lean)
"""
import itertools, os, sys
from fractions import Fraction
import sympy as sp

U = [1, 1, 1, -1, -1, -1]
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, '..', 'Conway7', 'Gen')

T111 = [[0,1,1],[1,0,1],[1,1,0]]
T112 = [[0,1,1],[1,0,2],[1,2,0]]
T113 = [[0,1,1],[1,0,3],[1,3,0]]
T122 = [[0,1,2],[1,0,2],[2,2,0]]
TNAME = {str(T111): '111', str(T112): '112', str(T113): '113', str(T122): '122'}

def block(P, Q, R):
    B = [[0]*6 for _ in range(6)]
    for i in range(3):
        for j in range(3):
            B[i][j] = P[i][j]; B[3+i][3+j] = Q[i][j]; B[i][3+j] = R[i][j]; B[3+j][i] = R[i][j]
    return B

def gblock(B):
    # G = 3C + 12I - 4J - 2uu^T on A ∪ B (zero diagonal of C): diagonal 12 - 4 - 2 = 6
    return [[6 if i == j else 3*B[i][j] - 4 - 2*U[i]*U[j] for j in range(6)] for i in range(6)]

def lin_int(e):
    return sp.Integer(e)

def choose_S(Gb):
    for S in itertools.combinations(range(6), 4):
        M = sp.Matrix([[Gb[a][b] for b in S] for a in S])
        d = M.det()
        if d != 0:
            assert d > 0
            return list(S), M.adjugate(), int(d)
    raise ValueError('rank < 4')

# ---------------------------------------------------------------------------------------------
# Lean emission helpers

def mat_lean(M):
    rows = [', '.join(str(int(M[i, j])) for j in range(M.shape[1])) for i in range(M.shape[0])]
    return '!![' + '; '.join(rows) + ']'

def poly_quad(Adj, nvars=4):
    """Σ_t (Σ_s (3 z_s - 4) Adj s t) (3 z_t - 4) as a Lean expression in z0..z3."""
    zs = sp.symbols('z0:4')
    X = [3*z - 4 for z in zs]
    e = sp.expand(sum(X[s]*Adj[s, t]*X[t] for s in range(4) for t in range(4)))
    return e, zs

def poly_lin(Adj, gcol):
    zs = sp.symbols('z0:4')
    X = [3*z - 4 for z in zs]
    e = sp.expand(sum(X[s]*Adj[s, t]*gcol[t] for s in range(4) for t in range(4)))
    return e, zs

def lean_poly(e, names):
    """sympy polynomial -> Lean ℤ expression (terms joined with + / -)."""
    p = sp.Poly(e, *names)
    terms = []
    for mon, coeff in p.terms():
        c = int(coeff)
        fac = []
        for v, k in zip(names, mon):
            fac += [str(v)] * k
        body = ' * '.join(fac)
        if body:
            terms.append((c, body))
        else:
            terms.append((c, None))
    s = ''
    for c, body in terms:
        a = abs(c)
        piece = (f'{a} * {body}' if a != 1 else body) if body else f'{a}'
        if s == '':
            s = ('-' if c < 0 else '') + piece
        else:
            s += (' - ' if c < 0 else ' + ') + piece
    return s or '0'

# ---------------------------------------------------------------------------------------------
# finite search mirrored from the Lean predicates

def mixed_solutions(B):
    Gb = gblock(B)
    S, Adj, D = choose_S(Gb)
    rest = [j for j in range(6) if j not in S]
    sols = []
    for z in itertools.product(range(5), repeat=4):
        X = [3*v - 4 for v in z]
        q = sum(X[s]*Adj[s, t]*X[t] for s in range(4) for t in range(4))
        if q != 8*D:
            continue
        row = [None]*6
        for s in range(4):
            row[S[s]] = z[s]
        ok = True
        for j in rest:
            L = sum(X[s]*Adj[s, t]*Gb[S[t]][j] for s in range(4) for t in range(4))
            w = (L + 4*D) // (3*D)
            if D*(3*w - 4) != L or not (0 <= w <= 4):
                ok = False; break
            row[j] = w
        if not ok:
            continue
        if row[0] + row[1] + row[2] != row[3] + row[4] + row[5]:
            continue
        sols.append(tuple(row))
    return S, Adj, D, rest, sols

def row_contradiction(B, sols):
    """Find a row r in A ∪ B such that the six mixed entries C r m, each in V_r, cannot have the
    required sum and square-sum. Returns (r, V, S, Q, kind)."""
    for r in range(6):
        V = sorted(set(s[r] for s in sols))
        Ssum = 12 - sum(B[r])
        Qsum = 24 - 2*U[r]*U[r] - sum(x*x for x in B[r])
        feas = any(sum(c) == Ssum and sum(x*x for x in c) == Qsum
                   for c in itertools.product(V, repeat=6))
        if feas:
            continue
        if len(V) <= 2:
            return r, V, Ssum, Qsum, 'two'
        if V == [0, 1, 3]:
            return r, V, Ssum, Qsum, '013'
    raise ValueError('no row contradiction found')

# ---------------------------------------------------------------------------------------------
# Lean emission: one block lemma (Section 8 of the paper)

ENT = [(i, j) for i in range(6) for j in range(i+1, 6)]   # 15 off-diagonal entries of the block

def hyp_name(i, j):
    return f'e{i}{j}'

def block_signature(B):
    return ' '.join(f'({hyp_name(i,j)} : C {i} {j} = {B[i][j]})' for (i, j) in ENT)

def block_simpset(B):
    """lines deriving the symmetric versions and the zero diagonal; returns (lines, names)"""
    lines, names = [], []
    for (i, j) in ENT:
        lines.append(f'  have {hyp_name(j,i)} : C {j} {i} = {B[i][j]} := by rw [hC.symm]; exact {hyp_name(i,j)}')
        names += [hyp_name(i, j), hyp_name(j, i)]
    for i in range(6):
        lines.append(f'  have {hyp_name(i,i)} : C {i} {i} = 0 := hC.diag {i}')
        names.append(hyp_name(i, i))
    return lines, names

def emit_block(name, B):
    S, Adj, D, rest, sols = mixed_solutions(B)
    r, V, Ssum, Qsum, kind = row_contradiction(B, sols)
    Gb = gblock(B)
    qe, zs = poly_quad(Adj)
    out = []
    out.append(f'/-! ### Block `{name}`: the `A ∪ B` block is {B} -/')
    out.append('')
    out.append(f'def qf_{name} (z0 z1 z2 z3 : ℤ) : ℤ := {lean_poly(qe, zs)}')
    for j in rest:
        le, _ = poly_lin(Adj, [Gb[S[t]][j] for t in range(4)])
        out.append(f'def l{j}_{name} (z0 z1 z2 z3 : ℤ) : ℤ := {lean_poly(le, zs)}')
    zargs = ' '.join(f'(zc v {s})' for s in range(4))
    def E(j):
        if j in S:
            return f'zc v {S.index(j)}'
        return f'wv (l{j}_{name} {zargs}) {D}'
    out.append('')
    out.append(f'def pred_{name} (v : Fin 4 → Fin 5) : Prop :=')
    out.append(f'  {D} * 8 = qf_{name} {zargs} →')
    for j in rest:
        L = f'l{j}_{name} {zargs}'
        out.append(f'  {D} * (3 * wv ({L}) {D} - 4) = {L} → 0 ≤ wv ({L}) {D} → wv ({L}) {D} ≤ 4 →')
    out.append(f'  {E(0)} + {E(1)} + {E(2)} = {E(3)} + {E(4)} + {E(5)} →')
    out.append('  ' + ' ∨ '.join(f'{E(r)} = {x}' for x in V))
    out.append('')
    out.append(f'instance (v : Fin 4 → Fin 5) : Decidable (pred_{name} v) := by unfold pred_{name}; infer_instance')
    out.append('')
    out.append(f'theorem pred_{name}_all : ∀ v, pred_{name} v := by decide +kernel')
    out.append('')
    lines, names = block_simpset(B)
    Sl = '![' + ', '.join(str(s) for s in S) + ']'
    simpB = ', '.join(names)
    out.append(f'theorem block_{name} (hC : IsOrbitMatrix C) {block_signature(B)} : False := by')
    out += lines
    out.append(f'  have hGS : GS {Sl} C = {mat_lean(sp.Matrix([[Gb[a][b] for b in S] for a in S]))} := by')
    out.append(f'    ext s t; fin_cases s <;> fin_cases t <;> simp [GS, G_apply, {simpB}]')
    out.append(f'  have hAdj : {mat_lean(Adj)} * GS {Sl} C = ({D} : ℤ) • 1 := by rw [hGS]; decide')
    out.append(f'  have hAdjT : ({mat_lean(Adj)} : Matrix (Fin 4) (Fin 4) ℤ)ᵀ = {mat_lean(Adj)} := by decide')
    out.append(f'  have hS : ∀ s, (({Sl} : Fin 4 → Fin 12) s).val < 6 := by decide')
    out.append(f'  have key : ∀ m : Fin 12, 6 ≤ m.val → ' + ' ∨ '.join(f'C m {r} = {x}' for x in V) + ' := by')
    out.append(f'    intro m hm')
    for s in range(4):
        out.append(f'    obtain ⟨n{s}, hn{s}⟩ := hC.nat5 m {S[s]}')
    out.append(f'    have hq := hC.fac_mm {Sl} _ {D} (by norm_num) hAdjT hAdj hS m hm')
    out.append(f'    simp only [Fin.sum_univ_four] at hq')
    out.append(f'    norm_num at hq')
    for j in rest:
        out.append(f'    have hl{j} := hC.fac_mj {Sl} _ {D} (by norm_num) hAdjT hAdj hS m hm {j} (by decide)')
        out.append(f'    simp only [Fin.sum_univ_four] at hl{j}')
        out.append(f'    norm_num [G_apply, {simpB}] at hl{j}')
    out.append(f'    have hcu := hC.usum_expand m')
    out.append(f'    have hp := pred_{name}_all ![n0, n1, n2, n3]')
    for s in range(4):
        out.append(f'    have z{s} : zc ![n0, n1, n2, n3] {s} = C m {S[s]} := by rw [hn{s}]; rfl')
    out.append(f'    unfold pred_{name} at hp')
    out.append(f'    rw [z0, z1, z2, z3] at hp')
    for j in rest:
        L = f'l{j}_{name} (C m {S[0]}) (C m {S[1]}) (C m {S[2]}) (C m {S[3]})'
        out.append(f'    have hL{j} : {D} * (3 * C m {j} - 4) = {L} := by unfold l{j}_{name}; linear_combination hl{j}')
        out.append(f'    have hw{j} : wv ({L}) {D} = C m {j} := ediv_of_mul_eq (by norm_num) hL{j}')
    out.append(f'    have hQ : {D} * 8 = qf_{name} (C m {S[0]}) (C m {S[1]}) (C m {S[2]}) (C m {S[3]}) := by')
    out.append(f'      unfold qf_{name}; linear_combination hq')
    args = ['hQ']
    for j in rest:
        args += [f'(by rw [hw{j}]; exact hL{j})', f'(by rw [hw{j}]; exact hC.nonneg m {j})',
                 f'(by rw [hw{j}]; exact hC.le4 m {j})']
    out.append(f'    have hp2 := hp ' + ' '.join(args))
    if rest:
        out.append(f'    simp only [' + ', '.join(f'hw{j}' for j in rest) + '] at hp2')
    out.append(f'    exact hp2 (by linarith)')
    out.append(f'  have hrow := hC.row_expand {r}')
    out.append(f'  have hsq := hC.sq_expand {r}')
    out.append(f'  simp only [{simpB}, u0, u1, u2, u3, u4, u5] at hrow hsq')
    for m in range(6, 12):
        out.append(f'  have k{m} : ' + ' ∨ '.join(f'C {r} {m} = {x}' for x in V)
                   + f' := by rw [hC.symm]; exact key {m} (by decide)')
        if kind == 'two':
            p = V[0]; q = V[-1]
            out.append(f'  have s{m} : C {r} {m} * C {r} {m} = {p+q} * C {r} {m} - {p*q} := by')
            out.append(f'    rcases k{m} with h | h <;> rw [h] <;> norm_num' if len(V) == 2 else
                       f'    rw [k{m}]; norm_num')
        else:
            out.append(f'  obtain ⟨t{m}, ht{m}, s{m}⟩ : ∃ t : ℤ, (t = 0 ∨ t = 1) ∧ C {r} {m} * C {r} {m} = C {r} {m} + 6 * t := by')
            out.append(f'    rcases k{m} with h | h | h')
            out.append(f'    · exact ⟨0, Or.inl rfl, by rw [h]; norm_num⟩')
            out.append(f'    · exact ⟨0, Or.inl rfl, by rw [h]; norm_num⟩')
            out.append(f'    · exact ⟨1, Or.inr rfl, by rw [h]; norm_num⟩')
    out.append(f'  rw [' + ', '.join(f's{m}' for m in range(6, 12)) + '] at hsq')
    out.append(f'  omega')
    out.append('')
    return '\n'.join(out), dict(S=S, D=D, r=r, V=V, nsol=len(sols), kind=kind)

HEADER = '''import Conway7.Core

/-!
# Generated by `scripts/gen_core.py` -- do not edit by hand.
{doc}
-/

open Matrix Finset

namespace Conway7

variable {{C : Matrix (Fin 12) (Fin 12) ℤ}}

'''

# ---------------------------------------------------------------------------------------------
# Census of the block R (Section 7 of the paper)

def all_symm_names():
    """simp lemma names for the symmetric versions C j i = C i j (i < j < 6) of the R entries"""
    return [f's{j}{i}' for i in range(6) for j in range(i+1, 6)]

def symm_lines():
    return [f'  have s{j}{i} : C {j} {i} = C {i} {j} := hC.symm {j} {i}'
            for i in range(6) for j in range(i+1, 6)]

def rows_R(R):
    return [sum(r) for r in R]

def lean_list(tuples):
    return '[' + ', '.join('(' + ', '.join(f'({x} : ℤ)' if k == 0 else str(x) for k, x in enumerate(tp)) + ')'
                           for tp in tuples) + ']'

def emit_census_h3(block_names):
    """P = Q = T111: the line sums of R are 2; enumerate the 21 matrices R."""
    Rs = []
    for r03, r04, r13, r14 in itertools.product(range(5), repeat=4):
        r05 = 2 - r03 - r04; r15 = 2 - r13 - r14; r23 = 2 - r03 - r13; r24 = 2 - r04 - r14
        r25 = r03 + r04 + r13 + r14 - 2
        if min(r05, r15, r23, r24, r25) < 0:
            continue
        Rs.append(((r03, r04, r13, r14), [[r03, r04, r05], [r13, r14, r15], [r23, r24, r25]]))
    L = lean_list([k for k, _ in Rs])
    out = []
    out.append('def predR_h3 (v : Fin 4 → Fin 5) : Prop :=')
    out.append('  0 ≤ 2 - zc v 0 - zc v 1 → 0 ≤ 2 - zc v 2 - zc v 3 → 0 ≤ 2 - zc v 0 - zc v 2 →')
    out.append('  0 ≤ 2 - zc v 1 - zc v 3 → 0 ≤ zc v 0 + zc v 1 + zc v 2 + zc v 3 - 2 →')
    out.append(f'  (zc v 0, zc v 1, zc v 2, zc v 3) ∈ ({L} : List (ℤ × ℤ × ℤ × ℤ))')
    out.append('')
    out.append('instance (v : Fin 4 → Fin 5) : Decidable (predR_h3 v) := by unfold predR_h3; infer_instance')
    out.append('')
    out.append('theorem predR_h3_all : ∀ v, predR_h3 v := by decide +kernel')
    out.append('')
    out.append('theorem census_111_111 (hC : IsOrbitMatrix C) (p01 : C 0 1 = 1) (p02 : C 0 2 = 1)')
    out.append('    (p12 : C 1 2 = 1) (q34 : C 3 4 = 1) (q35 : C 3 5 = 1) (q45 : C 4 5 = 1) : False := by')
    out += symm_lines()
    out.append('  have p10 : C 1 0 = 1 := by rw [hC.symm]; exact p01')
    out.append('  have p20 : C 2 0 = 1 := by rw [hC.symm]; exact p02')
    out.append('  have p21 : C 2 1 = 1 := by rw [hC.symm]; exact p12')
    out.append('  have d0 := hC.diag 0; have d1 := hC.diag 1; have d2 := hC.diag 2')
    for k in (3, 4, 5):
        out.append(f'  have k{k} : C 0 {k} + C 1 {k} + C 2 {k} = 2 := by')
        out.append('    have hz : ∑ i, ∑ j, (![1, 1, 1] : Fin 3 → ℤ) i * (![1, 1, 1] : Fin 3 → ℤ) j *')
        out.append('        G C ((![0, 1, 2] : Fin 3 → Fin 12) i) ((![0, 1, 2] : Fin 3 → Fin 12) j) = 0 := by')
        out.append('      simp [Fin.sum_univ_three, G_apply, p01, p02, p12, p10, p20, p21, d0, d1, d2]')
        out.append(f'    have h := hC.comb_ker _ _ hz {k}')
        out.append(f'    simp [Fin.sum_univ_three, G_apply, {", ".join(all_symm_names())}] at h')
        out.append('    linarith')
    for a in (0, 1, 2):
        out.append(f'  have m{a} : C {a} 3 + C {a} 4 + C {a} 5 = 2 := by')
        out.append(f'    have h := hC.margin {a}')
        out.append(f'    simp only [p01, p02, p12, p10, p20, p21, d0, d1, d2] at h')
        out.append('    linarith')
    out.append('  have n05 := hC.nonneg 0 5; have n15 := hC.nonneg 1 5; have n23 := hC.nonneg 2 3')
    out.append('  have n24 := hC.nonneg 2 4; have n25 := hC.nonneg 2 5')
    out.append('  have f1 : 0 ≤ 2 - C 0 3 - C 0 4 := by omega')
    out.append('  have f2 : 0 ≤ 2 - C 1 3 - C 1 4 := by omega')
    out.append('  have f3 : 0 ≤ 2 - C 0 3 - C 1 3 := by omega')
    out.append('  have f4 : 0 ≤ 2 - C 0 4 - C 1 4 := by omega')
    out.append('  have f5 : 0 ≤ C 0 3 + C 0 4 + C 1 3 + C 1 4 - 2 := by omega')
    out.append(f'  have hd : (C 0 3, C 0 4, C 1 3, C 1 4) ∈ ({L} : List (ℤ × ℤ × ℤ × ℤ)) := by')
    for s, (i, j) in enumerate([(0, 3), (0, 4), (1, 3), (1, 4)]):
        out.append(f'    obtain ⟨n{s}, hn{s}⟩ := hC.nat5 {i} {j}')
    out.append('    have hp := predR_h3_all ![n0, n1, n2, n3]')
    for s, (i, j) in enumerate([(0, 3), (0, 4), (1, 3), (1, 4)]):
        out.append(f'    have z{s} : zc ![n0, n1, n2, n3] {s} = C {i} {j} := by rw [hn{s}]; rfl')
    out.append('    unfold predR_h3 at hp')
    out.append('    rw [z0, z1, z2, z3] at hp')
    out.append('    exact hp f1 f2 f3 f4 f5')
    out.append('  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hd')
    out.append('  rcases hd with ' + ' | '.join('⟨h0, h1, h2, h3⟩' for _ in Rs))
    for k, ((a, b, c, d), R) in enumerate(Rs):
        out.append(f'  · exact block_{block_names[k]} hC ' + ' '.join(['(by omega)'] * 15))
    out.append('')
    return '\n'.join(out), [R for _, R in Rs]

def GA_of(P):
    return sp.Matrix([[6 if i == j else 3*P[i][j] - 6 for j in range(3)] for i in range(3)])

def emit_census_h45(P, Q, tag, block_name_of):
    """P, Q canonical with h in {4,5}. Returns (lean text, list of labelled R found)."""
    GA = GA_of(P)
    AdjA = GA.adjugate(); DA = int(GA.det())
    assert DA > 0
    sA = [sum(P[i]) for i in range(3)]          # row sums of P = row sums of R
    sB = [sum(Q[i]) for i in range(3)]          # row sums of Q = column sums of R
    z = sp.symbols('z0:3')
    X = [3*zi - 2 for zi in z]
    w = [sum(AdjA[a, b]*X[b] for b in range(3)) for a in range(3)]
    coef = [-w[0], -w[1], -w[2], DA]            # residual of column b1 against A
    Gsym = [[GA[i, j] if (i < 3 and j < 3) else None for j in range(4)] for i in range(4)]
    for a in range(3):
        Gsym[a][3] = X[a]; Gsym[3][a] = X[a]
    Gsym[3][3] = 6
    al = sp.expand(sum(coef[i]*coef[j]*Gsym[i][j] for i in range(4) for j in range(4)))
    opts = []
    for c in itertools.product(range(5), repeat=3):
        if sum(c) != sB[0]:
            continue
        if al.subs(dict(zip(z, c))) >= 0:
            opts.append(c)
    t0, t1 = tag
    LO = lean_list(opts)
    out = []
    out.append(f'/-! ### Census for `P = T{t0}`, `Q = T{t1}` -/')
    out.append('')
    out.append(f'def al_{t0}_{t1} (z0 z1 z2 : ℤ) : ℤ := {lean_poly(al, z)}')
    out.append('')
    out.append(f'def predA_{t0}_{t1} (v : Fin 3 → Fin 5) : Prop :=')
    out.append(f'  zc v 0 + zc v 1 + zc v 2 = {sB[0]} → 0 ≤ al_{t0}_{t1} (zc v 0) (zc v 1) (zc v 2) →')
    out.append(f'  (zc v 0, zc v 1, zc v 2) ∈ ({LO} : List (ℤ × ℤ × ℤ))')
    out.append('')
    out.append(f'instance (v : Fin 3 → Fin 5) : Decidable (predA_{t0}_{t1} v) := by unfold predA_{t0}_{t1}; infer_instance')
    out.append('')
    out.append(f'theorem predA_{t0}_{t1}_all : ∀ v, predA_{t0}_{t1} v := by decide +kernel')
    out.append('')
    found = []
    per_opt = []
    y = sp.symbols('y0:6')   # c04 c14 c24 c05 c15 c25
    for k, o in enumerate(opts):
        Xo = [3*x - 2 for x in o]
        GS = sp.Matrix([[GA[i, j] for j in range(3)] + [Xo[i]] for i in range(3)] + [Xo + [6]])
        D = int(GS.det()); Adj = GS.adjugate()
        assert D > 0, (P, Q, o)
        col4 = [3*y[0] - 2, 3*y[1] - 2, 3*y[2] - 2, 3*Q[0][1] - 6]
        col5 = [3*y[3] - 2, 3*y[4] - 2, 3*y[5] - 2, 3*Q[0][2] - 6]
        f44 = sp.expand(sum(col4[s]*Adj[s, t]*col4[t] for s in range(4) for t in range(4)))
        f55 = sp.expand(sum(col5[s]*Adj[s, t]*col5[t] for s in range(4) for t in range(4)))
        f45 = sp.expand(sum(col4[s]*Adj[s, t]*col5[t] for s in range(4) for t in range(4)))
        G45 = 3*Q[1][2] - 6
        allowed = []
        for a, b in itertools.product(range(5), repeat=2):
            c24 = sB[1] - a - b; c05 = sA[0] - o[0] - a; c15 = sA[1] - o[1] - b
            c25 = sB[2] - c05 - c15
            vals = [a, b, c24, c05, c15, c25]
            if not all(0 <= t <= 4 for t in vals[2:]):
                continue
            if o[2] + c24 + c25 != sA[2]:
                continue
            sub = dict(zip(y, vals))
            if f44.subs(sub) != 6*D or f55.subs(sub) != 6*D or f45.subs(sub) != G45*D:
                continue
            allowed.append((a, b))
            found.append([[o[0], a, c05], [o[1], b, c15], [o[2], c24, c25]])
        nm = f'{t0}_{t1}_{k}'
        der = {0: 'zc v 0', 1: 'zc v 1', 2: f'({sB[1]} - zc v 0 - zc v 1)',
               3: f'({sA[0]} - {o[0]} - zc v 0)', 4: f'({sA[1]} - {o[1]} - zc v 1)',
               5: f'({sB[2]} - ({sA[0]} - {o[0]} - zc v 0) - ({sA[1]} - {o[1]} - zc v 1))'}
        out.append(f'def f44_{nm} (y0 y1 y2 y3 y4 y5 : ℤ) : ℤ := {lean_poly(f44, y)}')
        out.append(f'def f55_{nm} (y0 y1 y2 y3 y4 y5 : ℤ) : ℤ := {lean_poly(f55, y)}')
        out.append(f'def f45_{nm} (y0 y1 y2 y3 y4 y5 : ℤ) : ℤ := {lean_poly(f45, y)}')
        yargs = ' '.join(f'({der[i]})' for i in range(6))
        out.append(f'def predB_{nm} (v : Fin 2 → Fin 5) : Prop :=')
        for i in range(2, 6):
            out.append(f'  0 ≤ {der[i]} → {der[i]} ≤ 4 →')
        out.append(f'  {o[2]} + {der[2]} + {der[5]} = {sA[2]} →')
        out.append(f'  {6*D} = f44_{nm} {yargs} → {6*D} = f55_{nm} {yargs} → {G45*D} = f45_{nm} {yargs} →')
        out.append(f'  (zc v 0, zc v 1) ∈ ({lean_list(allowed)} : List (ℤ × ℤ))')
        out.append('set_option synthInstance.maxHeartbeats 1000000 in')
        out.append('set_option synthInstance.maxSize 2048 in')
        out.append(f'instance (v : Fin 2 → Fin 5) : Decidable (predB_{nm} v) := by unfold predB_{nm}; infer_instance')
        out.append(f'theorem predB_{nm}_all : ∀ v, predB_{nm} v := by decide +kernel')
        out.append('')
        per_opt.append((k, o, nm, GS, Adj, D, allowed))
    out.append('set_option maxHeartbeats 4000000 in')
    out.append(f'theorem census_{t0}_{t1} (hC : IsOrbitMatrix C) (p01 : C 0 1 = {P[0][1]}) (p02 : C 0 2 = {P[0][2]})')
    out.append(f'    (p12 : C 1 2 = {P[1][2]}) (q34 : C 3 4 = {Q[0][1]}) (q35 : C 3 5 = {Q[0][2]}) (q45 : C 4 5 = {Q[1][2]}) : False := by')
    out += symm_lines()
    out.append('  have p10 : C 1 0 = C 0 1 := hC.symm 1 0; have p20 : C 2 0 = C 0 2 := hC.symm 2 0')
    out.append('  have p21 : C 2 1 = C 1 2 := hC.symm 2 1; have q43 : C 4 3 = C 3 4 := hC.symm 4 3')
    out.append('  have q53 : C 5 3 = C 3 5 := hC.symm 5 3; have q54 : C 5 4 = C 4 5 := hC.symm 5 4')
    out.append('  have d0 := hC.diag 0; have d1 := hC.diag 1; have d2 := hC.diag 2; have d3 := hC.diag 3')
    out.append('  have d4 := hC.diag 4; have d5 := hC.diag 5')
    simpE = ('p01, p02, p12, q34, q35, q45, d0, d1, d2, d3, d4, d5, ' +
             ', '.join(n for n in all_symm_names() if n not in ('s10', 's20', 's21', 's43', 's53', 's54')) +
             ', p10, p20, p21, q43, q53, q54')
    # margins in clean linear form
    for a in range(3):
        out.append(f'  have m{a} : C {a} 3 + C {a} 4 + C {a} 5 = {sA[a]} := by')
        out.append(f'    have h := hC.margin {a}; simp only [{simpE}] at h; linarith')
    for bb in range(3):
        b = 3 + bb
        out.append(f'  have m{b} : C 0 {b} + C 1 {b} + C 2 {b} = {sB[bb]} := by')
        out.append(f'    have h := hC.margin {b}; simp only [{simpE}] at h; linarith')
    for (i, j) in [(0, 3), (1, 3), (2, 3), (0, 4), (1, 4), (2, 4), (0, 5), (1, 5), (2, 5)]:
        out.append(f'  have b{i}{j} := hC.nonneg {i} {j}; have c{i}{j} := hC.le4 {i} {j}')
    cf = [f'-({AdjA[a,0]} * (3 * C 0 3 - 2) + {AdjA[a,1]} * (3 * C 1 3 - 2) + {AdjA[a,2]} * (3 * C 2 3 - 2))'
          for a in range(3)]
    out.append(f'  have ho : (C 0 3, C 1 3, C 2 3) ∈ ({LO} : List (ℤ × ℤ × ℤ)) := by')
    out.append(f'    have hal := hC.comb_nonneg ![0, 1, 2, 3] ![{cf[0]}, {cf[1]}, {cf[2]}, {DA}]')
    out.append(f'    simp only [Fin.sum_univ_four] at hal')
    out.append(f'    norm_num [G_apply, {simpE}] at hal')
    out.append(f'    have hal2 : 0 ≤ al_{t0}_{t1} (C 0 3) (C 1 3) (C 2 3) := by unfold al_{t0}_{t1}; linear_combination hal')
    for s, (i, j) in enumerate([(0, 3), (1, 3), (2, 3)]):
        out.append(f'    obtain ⟨n{s}, hn{s}⟩ := hC.nat5 {i} {j}')
    out.append(f'    have hpa := predA_{t0}_{t1}_all ![n0, n1, n2]')
    for s, (i, j) in enumerate([(0, 3), (1, 3), (2, 3)]):
        out.append(f'    have z{s} : zc ![n0, n1, n2] {s} = C {i} {j} := by rw [hn{s}]; rfl')
    out.append(f'    unfold predA_{t0}_{t1} at hpa')
    out.append(f'    rw [z0, z1, z2] at hpa')
    out.append(f'    exact hpa m3 hal2')
    if not opts:
        out.append('  exact absurd ho (by simp)')
        out.append('')
        return '\n'.join(out), found
    out.append('  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at ho')
    out.append(f'  rcases ho with ' + ' | '.join('⟨o0, o1, o2⟩' for _ in opts))
    for (k, o, nm, GS, Adj, D, allowed) in per_opt:
        out.append(f'  · -- column at b1 = {o}')
        out.append(f'    have hd : (C 0 4, C 1 4) ∈ ({lean_list(allowed)} : List (ℤ × ℤ)) := by')
        out.append(f'      have d24 : C 2 4 = {sB[1]} - C 0 4 - C 1 4 := by linarith')
        out.append(f'      have d05 : C 0 5 = {sA[0]} - {o[0]} - C 0 4 := by linarith')
        out.append(f'      have d15 : C 1 5 = {sA[1]} - {o[1]} - C 1 4 := by linarith')
        out.append(f'      have d25 : C 2 5 = {sB[2]} - ({sA[0]} - {o[0]} - C 0 4) - ({sA[1]} - {o[1]} - C 1 4) := by linarith')
        out.append(f'      have r1 : 0 ≤ {sB[1]} - C 0 4 - C 1 4 := by linarith')
        out.append(f'      have r2 : {sB[1]} - C 0 4 - C 1 4 ≤ 4 := by linarith')
        out.append(f'      have r3 : 0 ≤ {sA[0]} - {o[0]} - C 0 4 := by linarith')
        out.append(f'      have r4 : {sA[0]} - {o[0]} - C 0 4 ≤ 4 := by linarith')
        out.append(f'      have r5 : 0 ≤ {sA[1]} - {o[1]} - C 1 4 := by linarith')
        out.append(f'      have r6 : {sA[1]} - {o[1]} - C 1 4 ≤ 4 := by linarith')
        out.append(f'      have r7 : 0 ≤ {sB[2]} - ({sA[0]} - {o[0]} - C 0 4) - ({sA[1]} - {o[1]} - C 1 4) := by linarith')
        out.append(f'      have r8 : {sB[2]} - ({sA[0]} - {o[0]} - C 0 4) - ({sA[1]} - {o[1]} - C 1 4) ≤ 4 := by linarith')
        out.append(f'      have r9 : {o[2]} + ({sB[1]} - C 0 4 - C 1 4) + ({sB[2]} - ({sA[0]} - {o[0]} - C 0 4) - ({sA[1]} - {o[1]} - C 1 4)) = {sA[2]} := by linarith')
        out.append(f'      have hGS : GS ![0, 1, 2, 3] C = {mat_lean(GS)} := by')
        out.append(f'        ext s t; fin_cases s <;> fin_cases t <;> simp [GS, G_apply, o0, o1, o2, {simpE}]')
        out.append(f'      have hAdj : {mat_lean(Adj)} * GS ![0, 1, 2, 3] C = ({D} : ℤ) • 1 := by rw [hGS]; decide')
        out.append(f'      have hAdjT : ({mat_lean(Adj)} : Matrix (Fin 4) (Fin 4) ℤ)ᵀ = {mat_lean(Adj)} := by decide')
        for (i, j) in [(4, 4), (5, 5), (4, 5)]:
            out.append(f'      have h{i}{j} := hC.factor_apply ![0, 1, 2, 3] _ {D} (by norm_num) hAdjT hAdj {i} {j}')
            out.append(f'      simp only [Fin.sum_univ_four] at h{i}{j}')
            out.append(f'      norm_num [G_apply, o0, o1, o2, {simpE}] at h{i}{j}')
        G45 = 3*Q[1][2] - 6
        for (ij, val) in [('44', 6*D), ('55', 6*D), ('45', G45*D)]:
            out.append(f'      have g{ij} : {val} = f{ij}_{nm} (C 0 4) (C 1 4) (C 2 4) (C 0 5) (C 1 5) (C 2 5) := by')
            out.append(f'        unfold f{ij}_{nm}; linear_combination h{ij}')
        out.append(f'      rw [d24, d05, d15, d25] at g44 g55 g45')
        out.append(f'      obtain ⟨n4, hn4⟩ := hC.nat5 0 4')
        out.append(f'      obtain ⟨n5, hn5⟩ := hC.nat5 1 4')
        out.append(f'      have hpb := predB_{nm}_all ![n4, n5]')
        out.append(f'      have z4 : zc ![n4, n5] 0 = C 0 4 := by rw [hn4]; rfl')
        out.append(f'      have z5 : zc ![n4, n5] 1 = C 1 4 := by rw [hn5]; rfl')
        out.append(f'      unfold predB_{nm} at hpb')
        out.append(f'      rw [z4, z5] at hpb')
        out.append(f'      exact hpb r1 r2 r3 r4 r5 r6 r7 r8 r9 g44 g55 g45')
        if not allowed:
            out.append('    exact absurd hd (by simp)')
            continue
        out.append('    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hd')
        out.append(f'    rcases hd with ' + ' | '.join('⟨a0, a1⟩' for _ in allowed))
        for (a, b) in allowed:
            c24 = sB[1] - a - b; c05 = sA[0] - o[0] - a; c15 = sA[1] - o[1] - b
            c25 = sB[2] - c05 - c15
            R = [[o[0], a, c05], [o[1], b, c15], [o[2], c24, c25]]
            bn = block_name_of(P, Q, R)
            out.append(f'    · exact block_{bn} hC ' + ' '.join(['(by omega)'] * 15))
    out.append('')
    return '\n'.join(out), found

# ---------------------------------------------------------------------------------------------
# driver

def main():
    os.makedirs(OUT, exist_ok=True)
    registry = {}       # str(B) -> name
    order = []
    def name_of(P, Q, R):
        B = block(P, Q, R)
        key = str(B)
        if key not in registry:
            registry[key] = f'b{len(order)}'
            order.append(B)
        return registry[key]
    # census texts (this also registers the blocks)
    h3_txt, h3_Rs = None, None
    # register h3 blocks first, in the census order
    Rs3 = []
    for r03, r04, r13, r14 in itertools.product(range(5), repeat=4):
        r05 = 2 - r03 - r04; r15 = 2 - r13 - r14; r23 = 2 - r03 - r13; r24 = 2 - r04 - r14
        r25 = r03 + r04 + r13 + r14 - 2
        if min(r05, r15, r23, r24, r25) < 0:
            continue
        Rs3.append([[r03, r04, r05], [r13, r14, r15], [r23, r24, r25]])
    names3 = [name_of(T111, T111, R) for R in Rs3]
    h3_txt, _ = emit_census_h3(names3)
    cen = []
    report = []
    for (P, Q, tag) in [(T112, T112, ('112', '112')), (T113, T113, ('113', '113')),
                        (T113, T122, ('113', '122')), (T122, T113, ('122', '113')),
                        (T122, T122, ('122', '122'))]:
        txt, found = emit_census_h45(P, Q, tag, name_of)
        cen.append(txt)
        report.append((tag, found))
    # blocks, split into files of at most 8 blocks
    infos = []
    files = []
    chunk = 8
    for f0 in range(0, len(order), chunk):
        parts = []
        for k in range(f0, min(f0 + chunk, len(order))):
            txt, info = emit_block(f'b{k}', order[k])
            parts.append(txt)
            infos.append((f'b{k}', info))
        fname = f'Blocks{f0 // chunk}'
        files.append(fname)
        with open(os.path.join(OUT, fname + '.lean'), 'w', encoding='utf8') as f:
            f.write(HEADER.format(doc=f'Section 8 of the paper: the mixed orbits, for blocks {f0}..{min(f0+chunk, len(order))-1}.')
                    + '\n\n'.join(parts) + '\nend Conway7\n')
    imports = '\n'.join(f'import Conway7.Gen.{f}' for f in files)
    with open(os.path.join(OUT, 'Census.lean'), 'w', encoding='utf8') as f:
        f.write(HEADER.format(doc='Section 7 of the paper: the census of the block `R`.').replace(
            'import Conway7.Core', imports) + h3_txt + '\n' + '\n'.join(cen) + '\nend Conway7\n')
    print('blocks:', len(order))
    for nm, info in infos:
        print(nm, info)
    for tag, found in report:
        print('census', tag, found)

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'test':
        B = block(T111, T111, [[2,0,0],[0,2,0],[0,0,2]])
        txt, info = emit_block('c1', B)
        os.makedirs(OUT, exist_ok=True)
        with open(os.path.join(OUT, 'Test.lean'), 'w', encoding='utf8') as f:
            f.write(HEADER.format(doc='Test block.') + txt + '\nend Conway7\n')
        print(info)
    else:
        main()
