import Ordre7.Imports

/-!
# The exterior quotient matrix of an order-7 automorphism: basic algebra

`C` is the symmetric `12 × 12` exterior orbit matrix, the indices `0,1,2` are the `LL`-orbits
(`u = 1`), `3,4,5` the `RR`-orbits (`u = -1`), `6,…,11` the mixed orbits (`u = 0`).

We prove the general tools used in the case analysis:
* `G = 3C + 12I - 4J - 2uuᵀ` satisfies `G * G = 21 • G`;
* positivity: `0 ≤ y ⬝ᵥ G *ᵥ y`, and `y ⬝ᵥ G *ᵥ y = 0 → G *ᵥ y = 0`;
* the trace-zero factorization: if `S` picks four indices whose Gram block has adjugate `Adj`
  (`Adj * G_S = D • 1`, `D > 0`), then `D • G = G_{·,S} * Adj * G_{S,·}` (this is where
  `tr G = 84`, i.e. the zero diagonal, is used: it encodes `rank G = 4`).
-/

open Matrix Finset

namespace Ordre7

/-- The sign vector `u = (1,1,1,-1,-1,-1,0,0,0,0,0,0)`. -/
def u : Fin 12 → ℤ := ![1, 1, 1, -1, -1, -1, 0, 0, 0, 0, 0, 0]

/-- Hypotheses on the exterior quotient matrix (zero diagonal included). -/
structure IsOrbitMatrix (C : Matrix (Fin 12) (Fin 12) ℤ) : Prop where
  symm : ∀ i j, C i j = C j i
  nonneg : ∀ i j, 0 ≤ C i j
  diag : ∀ i, C i i = 0
  row : ∀ i, ∑ j, C i j = 12
  usum : ∀ i, ∑ j, C i j * u j = 0
  sq : ∀ i j, ∑ k, C i k * C k j + C i j = (if i = j then 12 else 0) + 12 - 2 * (u i * u j)

/-- all-ones matrix -/
def J : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of fun _ _ => 1

/-- `uuᵀ` -/
def U : Matrix (Fin 12) (Fin 12) ℤ := Matrix.of fun i j => u i * u j

/-- The Gram matrix `G = 3C + 12I - 4J - 2uuᵀ`. -/
def G (C : Matrix (Fin 12) (Fin 12) ℤ) : Matrix (Fin 12) (Fin 12) ℤ :=
  (3 : ℤ) • C + (12 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) - (4 : ℤ) • J - (2 : ℤ) • U

lemma G_apply (C : Matrix (Fin 12) (Fin 12) ℤ) (i j : Fin 12) :
    G C i j = 3 * C i j + (if i = j then 12 else 0) - 4 - 2 * (u i * u j) := by
  simp only [G, J, U, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply, smul_eq_mul]
  split_ifs <;> ring

@[simp] lemma u0 : u 0 = 1 := rfl
@[simp] lemma u1 : u 1 = 1 := rfl
@[simp] lemma u2 : u 2 = 1 := rfl
@[simp] lemma u3 : u 3 = -1 := rfl
@[simp] lemma u4 : u 4 = -1 := rfl
@[simp] lemma u5 : u 5 = -1 := rfl
@[simp] lemma u6 : u 6 = 0 := rfl
@[simp] lemma u7 : u 7 = 0 := rfl
@[simp] lemma u8 : u 8 = 0 := rfl
@[simp] lemma u9 : u 9 = 0 := rfl
@[simp] lemma u10 : u 10 = 0 := rfl
@[simp] lemma u11 : u 11 = 0 := rfl

lemma u_of_ge6 (m : Fin 12) (hm : 6 ≤ m.val) : u m = 0 := by
  fin_cases m <;> simp_all

lemma ne_of_ge6 (m : Fin 12) (hm : 6 ≤ m.val) (k : Fin 12) (hk : k.val < 6) : m ≠ k := by
  intro h; subst h; omega

lemma u_sum : ∑ i, u i = 0 := by decide

lemma u_sq_sum : ∑ i, u i * u i = 6 := by decide

lemma sum12 (f : Fin 12 → ℤ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp [Fin.sum_univ_succ]
  ring

variable {C : Matrix (Fin 12) (Fin 12) ℤ}

namespace IsOrbitMatrix

variable (hC : IsOrbitMatrix C)
include hC

lemma sq_row (i : Fin 12) : ∑ k, C i k * C i k = 24 - 2 * (u i * u i) := by
  have h := hC.sq i i
  simp only [hC.diag i, ite_true, add_zero] at h
  have e : ∑ k, C i k * C i k = ∑ k, C i k * C k i :=
    Finset.sum_congr rfl (fun k _ => by rw [hC.symm k i])
  linarith

lemma row_expand (i : Fin 12) :
    C i 0 + C i 1 + C i 2 + C i 3 + C i 4 + C i 5 + C i 6 + C i 7 + C i 8 + C i 9 + C i 10 +
      C i 11 = 12 := by
  rw [← sum12]; exact hC.row i

lemma usum_expand (i : Fin 12) : C i 0 + C i 1 + C i 2 - C i 3 - C i 4 - C i 5 = 0 := by
  have h := hC.usum i
  rw [sum12] at h
  simp only [u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11] at h
  linarith

lemma sq_expand (i : Fin 12) :
    C i 0 * C i 0 + C i 1 * C i 1 + C i 2 * C i 2 + C i 3 * C i 3 + C i 4 * C i 4 + C i 5 * C i 5 +
      C i 6 * C i 6 + C i 7 * C i 7 + C i 8 * C i 8 + C i 9 * C i 9 + C i 10 * C i 10 +
      C i 11 * C i 11 = 24 - 2 * (u i * u i) := by
  have h := hC.sq_row i
  rw [sum12] at h
  exact h

lemma le4 (i j : Fin 12) : C i j ≤ 4 := by
  have h := hC.sq_row i
  have hu2 : 0 ≤ u i * u i := mul_self_nonneg _
  have hle : C i j * C i j ≤ ∑ k, C i k * C i k :=
    Finset.single_le_sum (f := fun k => C i k * C i k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ j)
  have h0 := hC.nonneg i j
  nlinarith

lemma col (j : Fin 12) : ∑ i, C i j = 12 := by
  simpa [hC.symm _ j] using hC.row j

lemma ucol (j : Fin 12) : ∑ i, u i * C i j = 0 := by
  have := hC.usum j
  simpa [hC.symm _ j, mul_comm] using this

lemma transpose_eq : Cᵀ = C := by
  ext i j; simp [hC.symm j i]

lemma mul_J : C * J = (12 : ℤ) • J := by
  ext i j; simp [Matrix.mul_apply, J, hC.row i]

lemma J_mul : J * C = (12 : ℤ) • J := by
  ext i j; simp [Matrix.mul_apply, J, hC.col j]

lemma mul_U : C * U = 0 := by
  ext i j
  simp only [Matrix.mul_apply, U, Matrix.of_apply, Matrix.zero_apply]
  have := hC.usum i
  calc ∑ k, C i k * (u k * u j) = (∑ k, C i k * u k) * u j := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = 0 := by rw [this, zero_mul]

lemma U_mul : U * C = 0 := by
  ext i j
  simp only [Matrix.mul_apply, U, Matrix.of_apply, Matrix.zero_apply]
  have := hC.ucol j
  calc ∑ k, u i * u k * C k j = u i * ∑ k, u k * C k j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = 0 := by rw [this, mul_zero]

lemma mul_self :
    C * C = (12 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) + (12 : ℤ) • J - (2 : ℤ) • U - C := by
  ext i j
  have := hC.sq i j
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, J, U, Matrix.of_apply, smul_eq_mul] at this ⊢
  split_ifs at this ⊢ <;> linarith

end IsOrbitMatrix

lemma J_mul_J : J * J = (12 : ℤ) • J := by
  ext i j; simp [Matrix.mul_apply, J]

lemma J_mul_U : J * U = 0 := by
  ext i j
  simp only [Matrix.mul_apply, J, U, Matrix.of_apply, Matrix.zero_apply, one_mul]
  rw [← Finset.sum_mul, u_sum, zero_mul]

lemma U_mul_J : U * J = 0 := by
  ext i j
  simp only [Matrix.mul_apply, J, U, Matrix.of_apply, Matrix.zero_apply, mul_one]
  rw [← Finset.mul_sum, u_sum, mul_zero]

lemma U_mul_U : U * U = (6 : ℤ) • U := by
  ext i j
  simp only [Matrix.mul_apply, U, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ k, u i * u k * (u k * u j) = u i * u j * ∑ k, u k * u k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = 6 * (u i * u j) := by rw [u_sq_sum]; ring

namespace IsOrbitMatrix

variable (hC : IsOrbitMatrix C)
include hC

/-- `G² = 21 G`. -/
lemma G_mul_G : G C * G C = (21 : ℤ) • G C := by
  have h1 := hC.mul_J
  have h2 := hC.J_mul
  have h3 := hC.mul_U
  have h4 := hC.U_mul
  have h5 := hC.mul_self
  simp only [G, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul,
    Matrix.mul_one, h1, h2, h3, h4, h5, J_mul_J, J_mul_U, U_mul_J, U_mul_U, smul_zero, smul_add,
    smul_sub, smul_smul]
  module

lemma G_symm (i j : Fin 12) : G C i j = G C j i := by
  rw [G_apply, G_apply, hC.symm i j, mul_comm (u i) (u j)]
  by_cases h : i = j
  · subst h; rfl
  · simp [h, Ne.symm h]

lemma G_transpose : (G C)ᵀ = G C := by
  ext i j; simp [hC.G_symm j i]

lemma trace_G : Matrix.trace (G C) = 84 := by
  simp only [Matrix.trace, Matrix.diag, G_apply, hC.diag, ite_true]
  decide

/-- `|G y|² = 21 · yᵀ G y`. -/
lemma Gy_dot (y : Fin 12 → ℤ) :
    (G C *ᵥ y) ⬝ᵥ (G C *ᵥ y) = 21 * (y ⬝ᵥ (G C *ᵥ y)) := by
  have h1 : (G C *ᵥ y) ⬝ᵥ (G C *ᵥ y) = ((G C *ᵥ y) ᵥ* G C) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
  have h2 : (G C *ᵥ y) ᵥ* G C = (21 : ℤ) • (G C *ᵥ y) := by
    rw [← Matrix.mulVec_transpose, hC.G_transpose, Matrix.mulVec_mulVec, hC.G_mul_G,
      Matrix.smul_mulVec]
  rw [h1, h2, smul_dotProduct, dotProduct_comm, smul_eq_mul]

lemma dot_self_nonneg (v : Fin 12 → ℤ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

lemma quad_nonneg (y : Fin 12 → ℤ) : 0 ≤ y ⬝ᵥ (G C *ᵥ y) := by
  have := hC.Gy_dot y
  have h0 := hC.dot_self_nonneg (G C *ᵥ y)
  linarith

lemma quad_zero (y : Fin 12 → ℤ) (hy : y ⬝ᵥ (G C *ᵥ y) = 0) (i : Fin 12) :
    (G C *ᵥ y) i = 0 := by
  have h := hC.Gy_dot y
  rw [hy, mul_zero] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg ((G C *ᵥ y) j))).mp h i
    (Finset.mem_univ _)
  exact mul_self_eq_zero.mp this

end IsOrbitMatrix

/-! ### Trace-zero factorization (rank 4) -/

section factor

variable (S : Fin 4 → Fin 12) (Adj : Matrix (Fin 4) (Fin 4) ℤ) (D : ℤ)

/-- columns of `G` at `S` -/
def Gc (C : Matrix (Fin 12) (Fin 12) ℤ) : Matrix (Fin 12) (Fin 4) ℤ := (G C).submatrix id S
/-- rows of `G` at `S` -/
def Gr (C : Matrix (Fin 12) (Fin 12) ℤ) : Matrix (Fin 4) (Fin 12) ℤ := (G C).submatrix S id
/-- principal block of `G` at `S` -/
def GS (C : Matrix (Fin 12) (Fin 12) ℤ) : Matrix (Fin 4) (Fin 4) ℤ := (G C).submatrix S S

namespace IsOrbitMatrix

variable (hC : IsOrbitMatrix C)
include hC

lemma G_mul_Gc : G C * Gc S C = (21 : ℤ) • Gc S C := by
  have h := hC.G_mul_G
  ext i s
  have := congrFun (congrFun h i) (S s)
  simpa [Gc, Matrix.mul_apply] using this

lemma Gr_mul_G : Gr S C * G C = (21 : ℤ) • Gr S C := by
  have h := hC.G_mul_G
  ext s j
  have := congrFun (congrFun h (S s)) j
  simpa [Gr, Matrix.mul_apply] using this

lemma Gr_mul_Gc : Gr S C * Gc S C = (21 : ℤ) • GS S C := by
  have h := hC.G_mul_G
  ext s t
  have := congrFun (congrFun h (S s)) (S t)
  simpa [Gr, Gc, GS, Matrix.mul_apply] using this

lemma Gr_eq : Gr S C = (Gc S C)ᵀ := by
  ext s j; simp [Gr, Gc, hC.G_symm (S s) j]

/-- **Trace-zero factorization.** If `Adj` is a symmetric adjugate-like matrix of the principal
block `G_S` (`Adj * G_S = D • 1`, `D > 0`), then `D • G = G_{·,S} Adj G_{S,·}`. -/
theorem factor (hD : 0 < D) (hAdjT : Adjᵀ = Adj) (hAdj : Adj * GS S C = D • 1) :
    D • G C = Gc S C * Adj * Gr S C := by
  set K := Gc S C * Adj * Gr S C with hK
  set F := D • G C - K with hF
  have hGG := hC.G_mul_G
  have hGK : G C * K = (21 : ℤ) • K := by
    rw [hK, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC.G_mul_Gc, Matrix.smul_mul, Matrix.smul_mul]
  have hKG : K * G C = (21 : ℤ) • K := by
    rw [hK, Matrix.mul_assoc, hC.Gr_mul_G, Matrix.mul_smul]
  have hKK : K * K = (21 * D) • K := by
    have e : K * K = Gc S C * Adj * (Gr S C * Gc S C) * Adj * Gr S C := by
      simp only [hK, Matrix.mul_assoc]
    rw [e, hC.Gr_mul_Gc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc
      (Gc S C), hAdj, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, smul_smul]
  have hFF : F * F = (21 * D) • F := by
    rw [hF]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hGG, hGK, hKG, hKK, smul_sub,
      smul_smul]
    module
  have hFT : Fᵀ = F := by
    rw [hF, Matrix.transpose_sub, Matrix.transpose_smul, hC.G_transpose, hK,
      Matrix.transpose_mul, Matrix.transpose_mul, hAdjT, hC.Gr_eq, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  have htrK : Matrix.trace K = 84 * D := by
    rw [hK, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hC.Gr_mul_Gc, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_mul_comm, hAdj, Matrix.trace_smul, Matrix.trace_one]
    simp; ring
  have htrF : Matrix.trace F = 0 := by
    rw [hF, Matrix.trace_sub, Matrix.trace_smul, hC.trace_G, htrK, smul_eq_mul]; ring
  -- diagonal entries of `F` are nonnegative
  have hdiag : ∀ i, (21 * D) * F i i = ∑ k, F i k * F i k := by
    intro i
    have := congrFun (congrFun hFF i) i
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : F k i = F i k := by
      have := congrFun (congrFun hFT i) k
      simpa [Matrix.transpose_apply] using this
    rw [this]
  have hpos : (0 : ℤ) < 21 * D := by positivity
  have hFii : ∀ i, 0 ≤ F i i := by
    intro i
    have h1 := hdiag i
    have h2 : 0 ≤ ∑ k, F i k * F i k := Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
    by_contra hneg
    have : (21 * D) * F i i < 0 := mul_neg_of_pos_of_neg hpos (not_le.mp hneg)
    linarith
  have hsum : ∑ i, F i i = 0 := htrF
  have hzero : ∀ i, F i i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hFii j)).mp hsum i (Finset.mem_univ _)
  have hF0 : F = 0 := by
    ext i k
    have h1 := hdiag i
    rw [hzero i, mul_zero] at h1
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (F i j))).mp h1.symm k
      (Finset.mem_univ _)
    simpa using mul_self_eq_zero.mp this
  have := hF0
  rw [hF, sub_eq_zero] at this
  exact this

/-- Entrywise form of the factorization. -/
theorem factor_apply (hD : 0 < D) (hAdjT : Adjᵀ = Adj) (hAdj : Adj * GS S C = D • 1)
    (i j : Fin 12) :
    D * G C i j = ∑ t, (∑ s, G C i (S s) * Adj s t) * G C (S t) j := by
  have := congrFun (congrFun (hC.factor S Adj D hD hAdjT hAdj) i) j
  simpa [Matrix.mul_apply, Gc, Gr] using this

end IsOrbitMatrix

end factor

/-! ### Relabelling -/

namespace IsOrbitMatrix

/-- The hypotheses are invariant under a relabelling preserving `u`. -/
lemma perm (hC : IsOrbitMatrix C) (σ : Equiv.Perm (Fin 12)) (hσ : ∀ i, u (σ i) = u i) :
    IsOrbitMatrix (fun i j => C (σ i) (σ j)) where
  symm i j := hC.symm _ _
  nonneg i j := hC.nonneg _ _
  diag i := hC.diag _
  row i := by
    have := hC.row (σ i)
    rwa [← Equiv.sum_comp σ] at this
  usum i := by
    have := hC.usum (σ i)
    rw [← Equiv.sum_comp σ] at this
    simpa [hσ] using this
  sq i j := by
    have := hC.sq (σ i) (σ j)
    rw [← Equiv.sum_comp σ] at this
    simpa [hσ, σ.injective.eq_iff] using this

end IsOrbitMatrix

end Ordre7
