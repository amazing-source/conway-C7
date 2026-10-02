import Conway7.Quotient
import Conway7.Cyclo
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Module

/-!
# The spectral step (paper, Section 5)

Over `ℚ`, let `E` be the eigenspace of `A` for the eigenvalue `3`, and `T` the shift
`f ↦ f ∘ sh`. Then

* `E3 = (A + 4)/7 - (2/77) J` is the projection onto `E`, of trace `54`, so `dim E = 54`;
* `E3 Pf`, where `Pf` averages over the orbits, is the projection onto `E ∩ Fix T`, of trace
  `(∑_U bq U U + 42) / 7`;
* `T ^ 7 = 1`, so `dim E = dim (E ∩ Fix T) + 6 k` (`six_dvd_of_pow_seven_sub`).
-/

open Finset Matrix

namespace Conway7

/-- the shift on the relabelled vertex set -/
def sh : W → W
  | none => none
  | some (U, b) => some (U, b + 1)

/-- the inverse shift -/
def shi : W → W
  | none => none
  | some (U, b) => some (U, b - 1)

/-- the shift as a permutation -/
def shE : W ≃ W where
  toFun := sh
  invFun := shi
  left_inv w := by rcases w with _ | ⟨U, b⟩ <;> simp [sh, shi]
  right_inv w := by rcases w with _ | ⟨U, b⟩ <;> simp [sh, shi]

lemma card_W : Fintype.card W = 99 := by simp [ZMod.card]

variable {A : Matrix W W ℤ}

/-- shift invariance of the adjacency matrix -/
lemma Setting.sh_inv (hA : Setting A) (w v : W) : A (sh w) (sh v) = A w v := by
  rcases w with _ | ⟨U, b⟩ <;> rcases v with _ | ⟨V, c⟩
  · rfl
  · exact hA.shiftx V c
  · simp only [sh]; rw [hA.symm, hA.shiftx, hA.symm]
  · exact hA.shift U V b c

noncomputable section

def Aq (A : Matrix W W ℤ) : Matrix W W ℚ := A.map (Int.cast)
def Jq : Matrix W W ℚ := Matrix.of fun _ _ => 1
def E3 (A : Matrix W W ℤ) : Matrix W W ℚ := (1/7 : ℚ) • (Aq A + (4 : ℚ) • 1) - (2/77 : ℚ) • Jq

/-- averaging over the orbits -/
def Pf : Matrix W W ℚ := fun w w' =>
  match w, w' with
  | none, none => 1
  | some (U, _), some (V, _) => if U = V then 1/7 else 0
  | _, _ => 0

/-- `f ↦ f ∘ sh` -/
def Tlin : (W → ℚ) →ₗ[ℚ] (W → ℚ) := LinearMap.funLeft ℚ ℚ sh

lemma Tlin_apply (f : W → ℚ) (w : W) : Tlin f w = f (sh w) := rfl

lemma sh_iter7 (w : W) : sh^[7] w = w := by
  rcases w with _ | ⟨U, b⟩
  · rfl
  · simp only [Function.iterate_succ, Function.comp, Function.iterate_zero, id, sh]
    congr 2; ring_nf; rw [show (7 : ZMod 7) = 0 from rfl]; ring

lemma Tlin_pow7 : Tlin ^ 7 = 1 := by
  apply LinearMap.ext; intro f; funext w
  have : ∀ n : ℕ, (Tlin ^ n) f w = f (sh^[n] w) := by
    intro n
    induction n generalizing w with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      rw [show (Tlin ((Tlin ^ n) f)) w = (Tlin ^ n) f (sh w) from rfl, ih]
      rw [← Function.iterate_succ_apply' sh n w, Function.iterate_succ_apply]
  rw [this, sh_iter7]; rfl

lemma sum_sh (f : W → ℚ) : ∑ w, f (sh w) = ∑ w, f w :=
  Fintype.sum_equiv shE _ _ (fun _ => rfl)

lemma sum_Wq (f : W → ℚ) : ∑ w, f w = f none + ∑ U, ∑ b, f (some (U, b)) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]

namespace Setting

variable (hA : Setting A)
include hA

lemma Aq_sq : Aq A * Aq A + Aq A = (12 : ℚ) • (1 : Matrix W W ℚ) + (2 : ℚ) • Jq := by
  ext i j
  have h := hA.sq i j
  simp only [Aq, Matrix.add_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.one_apply, Jq, Matrix.of_apply, smul_eq_mul]
  have h' : ((∑ k, A i k * A k j + A i j : ℤ) : ℚ) = (((if i = j then 12 else 0) + 2 : ℤ) : ℚ) := by
    rw [h]
  push_cast at h'
  rw [h']
  split_ifs <;> norm_num

lemma Aq_J : Aq A * Jq = (14 : ℚ) • Jq := by
  ext i j
  simp only [Aq, Matrix.mul_apply, Matrix.map_apply, Jq, Matrix.of_apply, mul_one, Matrix.smul_apply,
    smul_eq_mul]
  have := hA.row14 i
  exact_mod_cast this

lemma J_Aq : Jq * Aq A = (14 : ℚ) • Jq := by
  ext i j
  simp only [Aq, Matrix.mul_apply, Matrix.map_apply, Jq, Matrix.of_apply, one_mul, Matrix.smul_apply,
    smul_eq_mul]
  have := hA.row14 j
  rw [Finset.sum_congr rfl (fun k _ => by rw [hA.symm k j])]
  exact_mod_cast this

lemma J_J : Jq * Jq = (99 : ℚ) • Jq := by
  ext i j
  simp [Jq, Matrix.mul_apply, card_W]

lemma Aq_E3 : Aq A * E3 A = (3 : ℚ) • E3 A := by
  have h1 := hA.Aq_sq
  have h2 := hA.Aq_J
  have e : Aq A * Aq A = (12 : ℚ) • (1 : Matrix W W ℚ) + (2 : ℚ) • Jq - Aq A := by
    rw [← h1]; abel
  simp only [E3, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, e, h2]
  module

lemma J_E3 : Jq * E3 A = 0 := by
  simp only [E3, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hA.J_Aq, hA.J_J]
  module

lemma E3_mul (M : Matrix W W ℚ) :
    E3 A * M = (1/7 : ℚ) • (Aq A * M + (4 : ℚ) • M) - (2/77 : ℚ) • (Jq * M) := by
  simp only [E3, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]

lemma E3_E3 : E3 A * E3 A = E3 A := by
  rw [hA.E3_mul, hA.Aq_E3, hA.J_E3]
  module

/-- the eigenspace for the eigenvalue `3` -/
def Eig (A : Matrix W W ℤ) : Submodule ℚ (W → ℚ) :=
  LinearMap.ker (Matrix.toLin' (Aq A - (3 : ℚ) • 1))

lemma mem_Eig (f : W → ℚ) : f ∈ Eig A ↔ Aq A *ᵥ f = (3 : ℚ) • f := by
  simp [Eig, Matrix.sub_mulVec, sub_eq_zero]

lemma E3_mem (f : W → ℚ) : E3 A *ᵥ f ∈ Eig A := by
  rw [hA.mem_Eig, Matrix.mulVec_mulVec, hA.Aq_E3, Matrix.smul_mulVec]

lemma E3_fix (f : W → ℚ) (hf : f ∈ Eig A) : E3 A *ᵥ f = f := by
  rw [hA.mem_Eig] at hf
  have hJ : Jq *ᵥ f = 0 := by
    have : Jq *ᵥ (Aq A *ᵥ f) = (14 : ℚ) • (Jq *ᵥ f) := by
      rw [Matrix.mulVec_mulVec, hA.J_Aq, Matrix.smul_mulVec]
    rw [hf, Matrix.mulVec_smul] at this
    have h11 : (11 : ℚ) • (Jq *ᵥ f) = 0 := by
      have := congrArg (fun v => v - (3 : ℚ) • (Jq *ᵥ f)) this
      simp only [sub_self] at this
      rw [eq_comm, ← sub_smul] at this
      norm_num at this ⊢
      exact this
    exact (smul_eq_zero.mp h11).resolve_left (by norm_num)
  simp only [E3, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hf, hJ,
    smul_zero, sub_zero]
  module

lemma isProj_E3 : LinearMap.IsProj (Eig A) (Matrix.toLin' (E3 A)) :=
  ⟨fun f => hA.E3_mem f, fun f hf => hA.E3_fix f hf⟩

lemma trace_E3 : Matrix.trace (E3 A) = 54 := by
  have hA0 : Matrix.trace (Aq A) = 0 := by
    simp [Matrix.trace, Aq, hA.diag]
  have hJ : Matrix.trace Jq = 99 := by simp [Matrix.trace, Jq, card_W]
  have h1 : Matrix.trace (1 : Matrix W W ℚ) = 99 := by simp [card_W]
  simp only [E3, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, hA0, hJ, h1, smul_eq_mul]
  norm_num

lemma finrank_Eig : Module.finrank ℚ (Eig A) = 54 := by
  have h := hA.isProj_E3.trace
  rw [Matrix.trace_toLin'_eq, hA.trace_E3] at h
  exact_mod_cast h.symm

/-! ### The shift -/

lemma Aq_comm (f : W → ℚ) : Aq A *ᵥ Tlin f = Tlin (Aq A *ᵥ f) := by
  ext w
  simp only [Tlin_apply, Matrix.mulVec, dotProduct, Aq, Matrix.map_apply]
  rw [← sum_sh (fun v => ((A (sh w) v : ℤ) : ℚ) * f v)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [hA.sh_inv]

lemma J_comm (f : W → ℚ) : Jq *ᵥ Tlin f = Tlin (Jq *ᵥ f) := by
  ext w
  simp only [Tlin_apply, Matrix.mulVec, dotProduct, Jq, Matrix.of_apply, one_mul]
  exact sum_sh f

lemma E3_comm (f : W → ℚ) : E3 A *ᵥ Tlin f = Tlin (E3 A *ᵥ f) := by
  simp only [E3, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    hA.Aq_comm, hA.J_comm, map_sub, map_add, map_smul]

lemma Eig_inv (f : W → ℚ) (hf : f ∈ Eig A) : Tlin f ∈ Eig A := by
  rw [hA.mem_Eig] at hf ⊢
  rw [hA.Aq_comm, hf, map_smul]

end Setting

/-- fixed vectors of the shift -/
def Fix : Submodule ℚ (W → ℚ) := LinearMap.ker (Tlin - 1)

lemma mem_Fix (f : W → ℚ) : f ∈ Fix ↔ ∀ w, f (sh w) = f w := by
  simp only [Fix, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h w; exact congrFun h w
  · intro h; ext w; exact h w

lemma Fix_const (f : W → ℚ) (hf : f ∈ Fix) (U : Fin 14) (b : ZMod 7) :
    f (some (U, b)) = f (some (U, 0)) := by
  rw [mem_Fix] at hf
  have key : ∀ n : ℕ, f (some (U, (n : ZMod 7))) = f (some (U, 0)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hf (some (U, (n : ZMod 7)))
      simp only [sh] at this
      push_cast; rw [this, ih]
  have := key b.val
  rwa [ZMod.natCast_zmod_val] at this

lemma Pf_sh (w v : W) : Pf (sh w) v = Pf w v := by
  rcases w with _ | ⟨U, b⟩ <;> rcases v with _ | ⟨V, c⟩ <;> rfl

lemma Pf_mem (f : W → ℚ) : Pf *ᵥ f ∈ Fix := by
  rw [mem_Fix]
  intro w
  simp only [Matrix.mulVec, dotProduct, Pf_sh]

lemma Pf_fix (f : W → ℚ) (hf : f ∈ Fix) : Pf *ᵥ f = f := by
  ext w
  rcases w with _ | ⟨U, b⟩
  · simp only [Matrix.mulVec, dotProduct]
    rw [sum_Wq]
    simp [Pf]
  · simp only [Matrix.mulVec, dotProduct]
    rw [sum_Wq]
    simp only [Pf, zero_mul, zero_add]
    rw [Finset.sum_eq_single U]
    · simp only [if_pos rfl]
      rw [Finset.sum_congr rfl (fun c _ => by rw [Fix_const f hf U c])]
      rw [Fix_const f hf U b]
      simp [ZMod.card]
    · intro V _ hV
      simp [Ne.symm hV]
    · simp

namespace Setting

variable (hA : Setting A)
include hA

lemma P2_mem (f : W → ℚ) : (E3 A * Pf) *ᵥ f ∈ Eig A ⊓ Fix := by
  rw [← Matrix.mulVec_mulVec]
  refine Submodule.mem_inf.mpr ⟨hA.E3_mem _, ?_⟩
  have h := Pf_mem f
  rw [mem_Fix] at h ⊢
  intro w
  have := congrFun (hA.E3_comm (Pf *ᵥ f)) w
  rw [Tlin_apply] at this
  have hT : Tlin (Pf *ᵥ f) = Pf *ᵥ f := by ext v; rw [Tlin_apply, h]
  rw [hT] at this
  exact this.symm

lemma P2_fix (f : W → ℚ) (hf : f ∈ Eig A ⊓ Fix) : (E3 A * Pf) *ᵥ f = f := by
  rw [← Matrix.mulVec_mulVec, Pf_fix f hf.2, hA.E3_fix f hf.1]

lemma isProj_P2 : LinearMap.IsProj (Eig A ⊓ Fix) (Matrix.toLin' (E3 A * Pf)) :=
  ⟨fun f => hA.P2_mem f, fun f hf => hA.P2_fix f hf⟩

lemma diag_AqPf_none : (Aq A * Pf) none none = 0 := by
  simp only [Matrix.mul_apply]
  rw [sum_Wq]
  simp [Pf, Aq, hA.diag]

lemma diag_AqPf_some (U : Fin 14) (b : ZMod 7) :
    (Aq A * Pf) (some (U, b)) (some (U, b)) = (bq A U U : ℚ) / 7 := by
  simp only [Matrix.mul_apply]
  rw [sum_Wq]
  simp only [Pf, mul_zero, zero_add]
  rw [Finset.sum_eq_single U]
  · simp only [ite_true]
    rw [← Finset.sum_mul]
    have h : (∑ c, (Aq A) (some (U, b)) (some (U, c))) = (bq A U U : ℚ) := by
      unfold bq Aq; simp only [Matrix.map_apply]; push_cast; exact_mod_cast hA.row_any U U b
    rw [h]; ring
  · intro V _ hV
    simp [hV]
  · simp

lemma trace_Aq_Pf : Matrix.trace (Aq A * Pf) = ∑ U, (bq A U U : ℚ) := by
  simp only [Matrix.trace, Matrix.diag]
  rw [sum_Wq, hA.diag_AqPf_none, zero_add]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  simp only [hA.diag_AqPf_some]
  simp [ZMod.card]
  ring

lemma trace_Pf : Matrix.trace Pf = 15 := by
  simp only [Matrix.trace, Matrix.diag]
  rw [sum_Wq]
  simp [Pf, ZMod.card]
  norm_num

lemma trace_J_Pf : Matrix.trace (Jq * Pf) = 99 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Jq, Matrix.of_apply, one_mul]
  rw [Finset.sum_comm]
  rw [sum_Wq]
  have e0 : ∑ w, Pf none w = 1 := by
    rw [sum_Wq]; simp [Pf]
  have e1 : ∀ U b, ∑ w, Pf (some (U, b)) w = 1 := by
    intro U b
    rw [sum_Wq]
    simp only [Pf, zero_add]
    rw [Finset.sum_eq_single U]
    · simp [ZMod.card]
    · intro V _ hV; simp [Ne.symm hV]
    · simp
  rw [e0]
  simp only [e1]
  simp [ZMod.card]
  norm_num

lemma trace_P2 : Matrix.trace (E3 A * Pf) = (∑ U, (bq A U U : ℚ) + 42) / 7 := by
  simp only [E3, Matrix.sub_mul, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_add, hA.trace_Aq_Pf, hA.trace_Pf, hA.trace_J_Pf, smul_eq_mul]
  ring

/-- **Spectral step.** `7 d = ∑ bq U U + 42` and `54 = d + 6 k`. -/
theorem spectral : ∃ d k : ℕ, 7 * (d : ℤ) = ∑ U, bq A U U + 42 ∧ 54 = d + 6 * k := by
  obtain ⟨k, hk⟩ := six_dvd_of_pow_seven_sub Tlin Tlin_pow7 (Eig A) hA.Eig_inv
  refine ⟨Module.finrank ℚ ↥(Eig A ⊓ Fix), k, ?_, ?_⟩
  · have h := hA.isProj_P2.trace
    rw [Matrix.trace_toLin'_eq, hA.trace_P2] at h
    have h7 : (7 : ℚ) * (Module.finrank ℚ ↥(Eig A ⊓ Fix) : ℚ) = ∑ U, (bq A U U : ℚ) + 42 := by
      rw [← h]; ring
    exact_mod_cast h7
  · rw [← hA.finrank_Eig, hk]
    rfl

end Setting

end

end Conway7
