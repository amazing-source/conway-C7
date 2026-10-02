import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# A linear map of order dividing 7 over `ℚ`

If `T` is a `ℚ`-linear endomorphism of a finite-dimensional space `E` with `T ^ 7 = 1`, then
`6 ∣ dim E - dim ker (T - 1)`.

Proof: `X ^ 7 - 1 = (X - 1) Φ₇` with coprime factors, so `E = ker (T - 1) ⊕ ker Φ₇(T)`. On
`W = ker Φ₇(T)` the polynomial ring acts through the field `K = ℚ[X] / (Φ₇)`, of degree `6` over
`ℚ`, so `dim_ℚ W = 6 · dim_K W`.
-/

open Polynomial Module

namespace Conway7

/-- A `ℚ`-linear endomorphism annihilated by `Φ₇` acts on a space of dimension divisible by 6. -/
theorem six_dvd_finrank_of_cyclotomic {W : Type*} [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W] (f : W →ₗ[ℚ] W) (hf : aeval f (cyclotomic 7 ℚ) = 0) :
    6 ∣ finrank ℚ W := by
  have hirr : Irreducible (cyclotomic 7 ℚ) := cyclotomic.irreducible_rat (by norm_num)
  -- `W` is torsion by `Φ₇` as a `ℚ[X]`-module
  have h1 : Module.IsTorsionBy ℚ[X] (Module.AEval' f) (cyclotomic 7 ℚ) := by
    intro m
    rw [← (Module.AEval'.of f).apply_symm_apply m, Module.AEval'.of, ← Module.AEval.of_aeval_smul]
    simp [hf]
  have htor : Module.IsTorsionBySet ℚ[X] (Module.AEval' f)
      (Ideal.span {cyclotomic 7 ℚ} : Set ℚ[X]) :=
    (Module.isTorsionBySet_iff_is_torsion_by_span _).mp
      ((Module.isTorsionBySet_singleton_iff _).mpr h1)
  let K := ℚ[X] ⧸ Ideal.span {cyclotomic 7 ℚ}
  have : (Ideal.span {cyclotomic 7 ℚ}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  letI : Field K := Ideal.Quotient.field _
  letI : Module K (Module.AEval' f) := Module.IsTorsionBySet.module htor
  have : IsScalarTower ℚ K (Module.AEval' f) := htor.isScalarTower (S := ℚ)
  have hK : finrank ℚ K = 6 := by
    have hne : cyclotomic 7 ℚ ≠ 0 := cyclotomic_ne_zero 7 ℚ
    have : finrank ℚ (AdjoinRoot (cyclotomic 7 ℚ)) = 6 := by
      rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, natDegree_cyclotomic]
      decide
    exact this
  haveI : FiniteDimensional ℚ (Module.AEval' f) :=
    LinearEquiv.finiteDimensional (Module.AEval'.of f)
  have htower := Module.finrank_mul_finrank ℚ K (Module.AEval' f)
  have heq : finrank ℚ (Module.AEval' f) = finrank ℚ W :=
    (LinearEquiv.finrank_eq (Module.AEval'.of f)).symm
  rw [hK, heq] at htower
  exact ⟨_, htower.symm⟩

/-- Evaluating a polynomial at the restriction of an endomorphism to an invariant subspace. -/
theorem aeval_restrict_apply {E : Type*} [AddCommGroup E] [Module ℚ E] (T : E →ₗ[ℚ] E)
    (W : Submodule ℚ E) (h : ∀ w ∈ W, T w ∈ W) (p : ℚ[X]) (w : W) :
    ((aeval (T.restrict h) p) w : E) = aeval T p (w : E) := by
  rw [aeval_endomorphism, aeval_endomorphism, Polynomial.sum, Polynomial.sum,
    Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Submodule.coe_smul, Module.End.pow_restrict, LinearMap.restrict_apply]

/-- **Lemma.** If `T ^ 7 = 1` on a finite-dimensional `ℚ`-space `E`, then
`6 ∣ dim E - dim ker (T - 1)`; more precisely `dim E = dim ker (T - 1) + 6 k`. -/
theorem six_dvd_of_pow_seven {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E) (hT : T ^ 7 = 1) :
    ∃ k, finrank ℚ E = finrank ℚ (LinearMap.ker (T - 1)) + 6 * k := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpq : IsCoprime (cyclotomic 1 ℚ) (cyclotomic 7 ℚ) := cyclotomic.isCoprime_rat (by norm_num)
  have hmul : cyclotomic 1 ℚ * cyclotomic 7 ℚ = X ^ 7 - 1 := by
    rw [mul_comm, cyclotomic_one, cyclotomic_prime_mul_X_sub_one]
  set p : ℚ[X] := cyclotomic 1 ℚ
  set q : ℚ[X] := cyclotomic 7 ℚ
  have hp : aeval T p = T - 1 := by simp [p]
  have htop : LinearMap.ker (aeval T (p * q)) = ⊤ := by
    rw [hmul]; simp [hT]
  have hsup := sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hpq
  have hdis := disjoint_ker_aeval_of_isCoprime T hpq
  rw [htop] at hsup
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (aeval T p))
    (LinearMap.ker (aeval T q))
  rw [hsup, hdis.eq_bot, finrank_bot, add_zero, finrank_top, hp] at hrank
  -- the restriction of `T` to `W = ker Φ₇(T)`
  set W := LinearMap.ker (aeval T q)
  have hW : ∀ w ∈ W, T w ∈ W := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hc : Commute T (aeval T q) := by
      simpa using (Polynomial.commute_X q).map (aeval T)
    rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hw, map_zero]
  have hf : aeval (T.restrict hW) q = 0 := by
    ext w
    rw [aeval_restrict_apply]
    simp
  obtain ⟨k, hk⟩ := six_dvd_finrank_of_cyclotomic (T.restrict hW) hf
  exact ⟨k, by rw [hrank, hk]⟩

/-- The same statement for a `T`-invariant subspace `E`: its dimension is that of its `T`-fixed
part plus a multiple of `6`. -/
theorem six_dvd_of_pow_seven_sub {M : Type*} [AddCommGroup M] [Module ℚ M] [FiniteDimensional ℚ M]
    (T : M →ₗ[ℚ] M) (hT : T ^ 7 = 1) (E : Submodule ℚ M) (hE : ∀ x ∈ E, T x ∈ E) :
    ∃ k, finrank ℚ E = finrank ℚ ↥(E ⊓ LinearMap.ker (T - 1)) + 6 * k := by
  set T' := T.restrict hE
  have hT' : T' ^ 7 = 1 := by
    rw [Module.End.pow_restrict]
    ext x
    simp [hT]
  obtain ⟨k, hk⟩ := six_dvd_of_pow_seven T' hT'
  have hsub : ∀ x ∈ E, (T - 1) x ∈ E := by
    intro x hx
    simpa using E.sub_mem (hE x hx) hx
  have hres : T' - 1 = (T - 1).restrict hsub := by
    ext x; simp [T']
  rw [hres, LinearMap.ker_restrict] at hk
  have hcomap : (LinearMap.ker (T - 1)).comap E.subtype = (E ⊓ LinearMap.ker (T - 1)).comap E.subtype := by
    ext x; simp
  rw [hcomap, (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq] at hk
  exact ⟨k, hk⟩

end Conway7
