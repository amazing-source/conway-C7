import Ordre7.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Set-up for the case analysis

* positivity / kernel statements for explicit integer combinations `∑ c_i e_{k_i}`;
* `G 1 = 0`, `G u = 0`, and `yᵀ G y ≤ 21 |y|²`;
* the `LL/RR` edge weights are `≥ 1` and their sum `h` lies in `[3,5]`;
* the margins `P1 = R1`, `Q1 = Rᵀ1`.
-/

open Matrix Finset

namespace Ordre7

/-- the integer combination `∑ c_i e_{k_i}` -/
def comb {n : ℕ} (e : Fin n → Fin 12) (c : Fin n → ℤ) : Fin 12 → ℤ :=
  ∑ i, c i • Pi.single (e i) (1 : ℤ)

lemma mulVec_comb {n : ℕ} (M : Matrix (Fin 12) (Fin 12) ℤ) (e : Fin n → Fin 12) (c : Fin n → ℤ)
    (k : Fin 12) : (M *ᵥ comb e c) k = ∑ j, c j * M k (e j) := by
  simp only [comb, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mulVec_smul, Pi.smul_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul]

lemma comb_dot {n : ℕ} (e : Fin n → Fin 12) (c : Fin n → ℤ) (v : Fin 12 → ℤ) :
    comb e c ⬝ᵥ v = ∑ i, c i * v (e i) := by
  simp only [comb, sum_dotProduct, smul_dotProduct, single_one_dotProduct, smul_eq_mul]

lemma quad_comb {n : ℕ} (M : Matrix (Fin 12) (Fin 12) ℤ) (e : Fin n → Fin 12) (c : Fin n → ℤ) :
    comb e c ⬝ᵥ (M *ᵥ comb e c) = ∑ i, ∑ j, c i * c j * M (e i) (e j) := by
  rw [comb_dot]
  simp only [mulVec_comb, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

variable {C : Matrix (Fin 12) (Fin 12) ℤ}

namespace IsOrbitMatrix

variable (hC : IsOrbitMatrix C)
include hC

lemma comb_nonneg {n : ℕ} (e : Fin n → Fin 12) (c : Fin n → ℤ) :
    0 ≤ ∑ i, ∑ j, c i * c j * G C (e i) (e j) := by
  rw [← quad_comb]; exact hC.quad_nonneg _

lemma comb_ker {n : ℕ} (e : Fin n → Fin 12) (c : Fin n → ℤ)
    (h : ∑ i, ∑ j, c i * c j * G C (e i) (e j) = 0) (k : Fin 12) :
    ∑ j, c j * G C k (e j) = 0 := by
  rw [← quad_comb] at h; rw [← mulVec_comb]; exact hC.quad_zero _ h k

lemma G_one : G C *ᵥ (fun _ => (1 : ℤ)) = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, mul_one, Pi.zero_apply, G_apply]
  rw [sum12]
  have h := hC.row_expand i
  have hd := hC.diag i
  fin_cases i <;> simp_all <;> linarith

lemma G_u : G C *ᵥ u = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, G_apply]
  rw [sum12]
  have h := hC.usum_expand i
  have hd := hC.diag i
  fin_cases i <;> simp_all <;> linarith

/-- `G ≤ 21 I` (as quadratic forms). -/
lemma quad_le (y : Fin 12 → ℤ) : y ⬝ᵥ (G C *ᵥ y) ≤ 21 * (y ⬝ᵥ y) := by
  have h1 := hC.Gy_dot y
  have h2 := hC.quad_nonneg y
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y (G C *ᵥ y)
  have e1 : y ⬝ᵥ (G C *ᵥ y) = ∑ i, y i * (G C *ᵥ y) i := rfl
  have e2 : y ⬝ᵥ y = ∑ i, y i ^ 2 := by
    simp only [dotProduct]; exact Finset.sum_congr rfl (fun i _ => (pow_two (y i)).symm)
  have e3 : (G C *ᵥ y) ⬝ᵥ (G C *ᵥ y) = ∑ i, (G C *ᵥ y) i ^ 2 := by
    simp only [dotProduct]; exact Finset.sum_congr rfl (fun i _ => (pow_two _).symm)
  rw [← e1, ← e2, ← e3, h1] at cs
  have hyy : 0 ≤ y ⬝ᵥ y := hC.dot_self_nonneg y
  nlinarith

/-! ### The `LL/RR` block -/

/-- No zero edge weight inside `A` or `B`. -/
lemma nozero (a a' b : Fin 12) (ε : ℤ) (hε : ε * ε = 1) (hne : a ≠ a') (hba : b ≠ a)
    (hba' : b ≠ a') (hua : u a = ε) (hua' : u a' = ε) (hub : u b = -ε) : 1 ≤ C a a' := by
  by_contra hlt
  have h0 : C a a' = 0 := by have := hC.nonneg a a'; omega
  have h0' : C a' a = 0 := by rw [hC.symm]; exact h0
  have hq : ∑ i, ∑ j, (![1, 1] : Fin 2 → ℤ) i * (![1, 1] : Fin 2 → ℤ) j *
      G C ((![a, a'] : Fin 2 → Fin 12) i) ((![a, a'] : Fin 2 → Fin 12) j) = 0 := by
    simp [Fin.sum_univ_two, G_apply, hC.diag, h0, h0', hne, Ne.symm hne, hua, hua']
    nlinarith [hε]
  have hk := hC.comb_ker _ _ hq b
  simp [Fin.sum_univ_two, G_apply, hba, hba', hua, hua', hub] at hk
  omega

lemma A_pos01 : 1 ≤ C 0 1 := hC.nozero 0 1 3 1 (by norm_num) (by decide) (by decide) (by decide)
  (by simp) (by simp) (by simp)
lemma A_pos02 : 1 ≤ C 0 2 := hC.nozero 0 2 3 1 (by norm_num) (by decide) (by decide) (by decide)
  (by simp) (by simp) (by simp)
lemma A_pos12 : 1 ≤ C 1 2 := hC.nozero 1 2 3 1 (by norm_num) (by decide) (by decide) (by decide)
  (by simp) (by simp) (by simp)
lemma B_pos34 : 1 ≤ C 3 4 := hC.nozero 3 4 0 (-1) (by norm_num) (by decide) (by decide)
  (by decide) (by simp) (by simp) (by simp)
lemma B_pos35 : 1 ≤ C 3 5 := hC.nozero 3 5 0 (-1) (by norm_num) (by decide) (by decide)
  (by decide) (by simp) (by simp) (by simp)
lemma B_pos45 : 1 ≤ C 4 5 := hC.nozero 4 5 0 (-1) (by norm_num) (by decide) (by decide)
  (by decide) (by simp) (by simp) (by simp)

/-- `eAᵀ G eA = 6h - 18`. -/
lemma quadA :
    ∑ i, ∑ j, (![1, 1, 1] : Fin 3 → ℤ) i * (![1, 1, 1] : Fin 3 → ℤ) j *
      G C ((![0, 1, 2] : Fin 3 → Fin 12) i) ((![0, 1, 2] : Fin 3 → Fin 12) j) =
      6 * (C 0 1 + C 0 2 + C 1 2) - 18 := by
  simp [Fin.sum_univ_three, G_apply, hC.diag, hC.symm 1 0, hC.symm 2 0, hC.symm 2 1]
  ring

lemma quadB :
    ∑ i, ∑ j, (![1, 1, 1] : Fin 3 → ℤ) i * (![1, 1, 1] : Fin 3 → ℤ) j *
      G C ((![3, 4, 5] : Fin 3 → Fin 12) i) ((![3, 4, 5] : Fin 3 → Fin 12) j) =
      6 * (C 3 4 + C 3 5 + C 4 5) - 18 := by
  simp [Fin.sum_univ_three, G_apply, hC.diag, hC.symm 4 3, hC.symm 5 3, hC.symm 5 4]
  ring

lemma h_ge : 3 ≤ C 0 1 + C 0 2 + C 1 2 := by
  have := hC.comb_nonneg ![0, 1, 2] ![1, 1, 1]
  rw [hC.quadA] at this
  omega

lemma h_le : C 0 1 + C 0 2 + C 1 2 ≤ 5 := by
  set eA := comb ![0, 1, 2] ![1, 1, 1] with heA
  set y : Fin 12 → ℤ := (4 : ℤ) • eA - (fun _ => 1) - (2 : ℤ) • u with hy
  have hGy : G C *ᵥ y = (4 : ℤ) • (G C *ᵥ eA) := by
    rw [hy, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hC.G_one, hC.G_u, smul_zero, sub_zero, sub_zero]
  have hsymm1 : (fun _ => (1 : ℤ)) ⬝ᵥ (G C *ᵥ eA) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hC.G_transpose, hC.G_one,
      zero_dotProduct]
  have hsymmu : u ⬝ᵥ (G C *ᵥ eA) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hC.G_transpose, hC.G_u,
      zero_dotProduct]
  have hq : y ⬝ᵥ (G C *ᵥ y) = 16 * (eA ⬝ᵥ (G C *ᵥ eA)) := by
    rw [hGy, dotProduct_smul, hy, sub_dotProduct, sub_dotProduct, smul_dotProduct,
      smul_dotProduct, hsymm1, hsymmu, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  have hyy : y ⬝ᵥ y = 12 := by
    rw [hy, heA]
    simp [comb, dotProduct, Fin.sum_univ_succ, Pi.single_apply]
  have hA : eA ⬝ᵥ (G C *ᵥ eA) = 6 * (C 0 1 + C 0 2 + C 1 2) - 18 := by
    rw [heA, quad_comb]; exact hC.quadA
  have := hC.quad_le y
  rw [hq, hyy, hA] at this
  omega

/-- margins: `R1 = P1` and `Rᵀ1 = Q1`, and `Σ Q = Σ P`. -/
lemma margin (a : Fin 12) : C a 0 + C a 1 + C a 2 = C a 3 + C a 4 + C a 5 := by
  have := hC.usum_expand a; linarith

lemma hQ_eq : C 3 4 + C 3 5 + C 4 5 = C 0 1 + C 0 2 + C 1 2 := by
  have m0 := hC.margin 0; have m1 := hC.margin 1; have m2 := hC.margin 2
  have m3 := hC.margin 3; have m4 := hC.margin 4; have m5 := hC.margin 5
  simp only [hC.diag] at m0 m1 m2 m3 m4 m5
  rw [hC.symm 1 0, hC.symm 2 0, hC.symm 2 1, hC.symm 3 0, hC.symm 3 1, hC.symm 3 2,
    hC.symm 4 0, hC.symm 4 1, hC.symm 4 2, hC.symm 5 0, hC.symm 5 1, hC.symm 5 2,
    hC.symm 4 3, hC.symm 5 3, hC.symm 5 4] at *
  linarith

end IsOrbitMatrix

end Ordre7
