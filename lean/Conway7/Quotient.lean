import Conway7.Core
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.BigOperators.Fin

/-!
# The orbit quotient of a shift-invariant srg(99,14,1,2) adjacency matrix

The vertex set is relabelled as `W = Option (Fin 14 × ZMod 7)`: `none` is the fixed vertex `x`, and
`some (U, b)` is the `b`-th vertex of the orbit `U`; the automorphism acts by `b ↦ b + 1`.

`Setting A` collects what we know about the adjacency matrix `A` in these coordinates. From it we
derive the identities satisfied by the orbit counts

* `t U = A x (U, 0)` (`x` is adjacent to the whole orbit `U` or to none of it),
* `bm U V = ∑ c, A (U, 0) (V, c)` (neighbours in the orbit `V` of a vertex of the orbit `U`),

collected in `QData t bm` (paper, Proposition 4.1, before the orbits are named).
-/

open Finset Matrix

namespace Conway7

/-- relabelled vertex set -/
abbrev W := Option (Fin 14 × ZMod 7)

/-- the hypotheses on the relabelled adjacency matrix -/
structure Setting (A : Matrix W W ℤ) : Prop where
  symm : ∀ i j, A i j = A j i
  zo : ∀ i j, A i j = 0 ∨ A i j = 1
  diag : ∀ i, A i i = 0
  sq : ∀ i j, ∑ k, A i k * A k j + A i j = (if i = j then 12 else 0) + 2
  shift : ∀ U V b c, A (some (U, b + 1)) (some (V, c + 1)) = A (some (U, b)) (some (V, c))
  shiftx : ∀ U b, A none (some (U, b + 1)) = A none (some (U, b))

/-- The quotient data (paper, Proposition 4.1 before the orbits are named). -/
structure QData (t : Fin 14 → ℤ) (bm : Matrix (Fin 14) (Fin 14) ℤ) : Prop where
  t01 : ∀ U, t U = 0 ∨ t U = 1
  nonneg : ∀ U V, 0 ≤ bm U V
  symm : ∀ U V, bm U V = bm V U
  row : ∀ U, ∑ V, bm U V + t U = 14
  tsum : ∑ U, t U = 2
  sq : ∀ U V, ∑ W, bm U W * bm W V + 7 * t U * t V + bm U V = (if U = V then 12 else 0) + 14
  xrow : ∀ V, ∑ W, t W * bm W V + t V = 2
  even : ∀ U, Even (bm U U)

/-- sums over `ZMod 7` are invariant under translation -/
lemma sum_zmod7_add (f : ZMod 7 → ℤ) (k : ZMod 7) : ∑ c, f (c + k) = ∑ c, f c :=
  Fintype.sum_equiv (Equiv.addRight k) _ _ (fun _ => rfl)

lemma sum_zmod7_neg (f : ZMod 7 → ℤ) : ∑ c, f (-c) = ∑ c, f c :=
  Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)

lemma sum_zmod7_expand (f : ZMod 7 → ℤ) :
    ∑ c, f c = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  exact Fin.sum_univ_seven f

/-- sum over the relabelled vertex set -/
lemma sum_W (f : W → ℤ) : ∑ w, f w = f none + ∑ U, ∑ b, f (some (U, b)) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]

variable {A : Matrix W W ℤ}

namespace Setting

variable (hA : Setting A)
include hA

/-- shift invariance by any amount -/
lemma shift_k (U V : Fin 14) (b c k : ZMod 7) :
    A (some (U, b + k)) (some (V, c + k)) = A (some (U, b)) (some (V, c)) := by
  have key : ∀ n : ℕ, A (some (U, b + n)) (some (V, c + n)) = A (some (U, b)) (some (V, c)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hA.shift U V (b + n) (c + n)
      rw [show b + ((n + 1 : ℕ) : ZMod 7) = b + n + 1 by push_cast; ring,
        show c + ((n + 1 : ℕ) : ZMod 7) = c + n + 1 by push_cast; ring, this, ih]
  have := key k.val
  rwa [ZMod.natCast_zmod_val] at this

lemma shiftx_k (U : Fin 14) (b k : ZMod 7) : A none (some (U, b + k)) = A none (some (U, b)) := by
  have key : ∀ n : ℕ, A none (some (U, b + n)) = A none (some (U, b)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hA.shiftx U (b + n)
      rw [show b + ((n + 1 : ℕ) : ZMod 7) = b + n + 1 by push_cast; ring, this, ih]
  have := key k.val
  rwa [ZMod.natCast_zmod_val] at this

/-- `x` is adjacent to all of an orbit or to none of it -/
lemma tx (U : Fin 14) (b : ZMod 7) : A none (some (U, b)) = A none (some (U, 0)) := by
  have := hA.shiftx_k U 0 b
  rwa [zero_add] at this

lemma xt (U : Fin 14) (b : ZMod 7) : A (some (U, b)) none = A none (some (U, 0)) := by
  rw [hA.symm, hA.tx]

lemma row_any (U V : Fin 14) (b : ZMod 7) :
    ∑ c, A (some (U, b)) (some (V, c)) = ∑ c, A (some (U, 0)) (some (V, c)) := by
  rw [← sum_zmod7_add (fun c => A (some (U, b)) (some (V, c))) b]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have := hA.shift_k U V 0 c b
  rw [zero_add] at this
  rw [this]

lemma row14 (i : W) : ∑ k, A i k = 14 := by
  have h := hA.sq i i
  rw [if_pos rfl, hA.diag i, add_zero] at h
  have e : ∑ k, A i k * A k i = ∑ k, A i k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hA.symm k i]
    rcases hA.zo i k with h0 | h1
    · rw [h0]; ring
    · rw [h1]; ring
  linarith

end Setting

/-- the orbit counts -/
def tq (A : Matrix W W ℤ) (U : Fin 14) : ℤ := A none (some (U, 0))

def bq (A : Matrix W W ℤ) : Matrix (Fin 14) (Fin 14) ℤ :=
  fun U V => ∑ c, A (some (U, 0)) (some (V, c))

namespace Setting

variable (hA : Setting A)
include hA

lemma bq_symm (U V : Fin 14) : bq A U V = bq A V U := by
  unfold bq
  rw [← sum_zmod7_neg]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [hA.symm]
  have := hA.shift_k V U (-c) 0 c
  rw [neg_add_cancel, zero_add] at this
  rw [← this]

lemma bq_even (U : Fin 14) : Even (bq A U U) := by
  unfold bq
  rw [sum_zmod7_expand]
  have hs : ∀ c : ZMod 7, A (some (U, 0)) (some (U, c)) = A (some (U, 0)) (some (U, -c)) := by
    intro c
    rw [hA.symm]
    have := hA.shift_k U U c 0 (-c)
    rw [add_neg_cancel, zero_add] at this
    rw [this]
  have h6 := hs 1; have h5 := hs 2; have h4 := hs 3
  have h0 := hA.diag (some (U, 0))
  rw [show (-1 : ZMod 7) = 6 by decide] at h6
  rw [show (-2 : ZMod 7) = 5 by decide] at h5
  rw [show (-3 : ZMod 7) = 4 by decide] at h4
  rw [h0, ← h6, ← h5, ← h4]
  exact ⟨A (some (U, 0)) (some (U, 1)) + A (some (U, 0)) (some (U, 2)) + A (some (U, 0)) (some (U, 3)),
    by ring⟩

lemma tq01 (U : Fin 14) : tq A U = 0 ∨ tq A U = 1 := hA.zo _ _

lemma bq_nonneg (U V : Fin 14) : 0 ≤ bq A U V := by
  unfold bq
  exact Finset.sum_nonneg (fun c _ => by rcases hA.zo (some (U, 0)) (some (V, c)) with h | h <;> rw [h] <;> norm_num)

lemma bq_row (U : Fin 14) : ∑ V, bq A U V + tq A U = 14 := by
  have h := hA.row14 (some (U, 0))
  rw [sum_W] at h
  unfold bq tq
  rw [hA.xt] at h
  linarith

lemma tq_sum : ∑ U, tq A U = 2 := by
  have h := hA.row14 none
  rw [sum_W, hA.diag] at h
  have e : ∀ U, ∑ b, A none (some (U, b)) = 7 * tq A U := by
    intro U
    unfold tq
    rw [Finset.sum_congr rfl (fun b _ => hA.tx U b)]
    simp
  rw [Finset.sum_congr rfl (fun U _ => e U), ← Finset.mul_sum] at h
  linarith

/-- the column sums of an orbit block -/
lemma col_sum (w : W) (V : Fin 14) :
    ∑ c, A w (some (V, c)) = match w with
      | none => 7 * tq A V
      | some (U, _) => bq A U V := by
  rcases w with _ | ⟨U, b⟩
  · simp only
    unfold tq
    rw [Finset.sum_congr rfl (fun b _ => hA.tx V b)]
    simp
  · simp only
    exact hA.row_any U V b

lemma bq_sq (U V : Fin 14) :
    ∑ W', bq A U W' * bq A W' V + 7 * tq A U * tq A V + bq A U V =
      (if U = V then 12 else 0) + 14 := by
  have h : ∑ c, (∑ k, A (some (U, 0)) k * A k (some (V, c)) + A (some (U, 0)) (some (V, c))) =
      ∑ c : ZMod 7, ((if some (U, (0 : ZMod 7)) = some (V, c) then (12 : ℤ) else 0) + 2) :=
    Finset.sum_congr rfl (fun c _ => hA.sq _ _)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at h
  have e1 : ∀ k : W, ∑ c, A (some (U, 0)) k * A k (some (V, c)) =
      A (some (U, 0)) k * ∑ c, A k (some (V, c)) := fun k => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => e1 k), sum_W] at h
  simp only [hA.col_sum] at h
  rw [hA.xt] at h
  have e2 : ∀ W' : Fin 14, ∑ b, A (some (U, 0)) (some (W', b)) * bq A W' V =
      bq A U W' * bq A W' V := fun W' => by unfold bq; rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun W' _ => e2 W')] at h
  have e3 : ∑ c : ZMod 7, ((if some (U, (0 : ZMod 7)) = some (V, c) then (12 : ℤ) else 0) + 2) =
      (if U = V then 12 else 0) + 14 := by
    rw [Finset.sum_add_distrib]
    by_cases hUV : U = V
    · subst hUV
      rw [Finset.sum_eq_single (0 : ZMod 7)]
      · simp
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · simp [hUV]
  rw [e3] at h
  unfold tq bq at *
  linarith

lemma xrow (V : Fin 14) : ∑ W', tq A W' * bq A W' V + tq A V = 2 := by
  have h : ∑ c, (∑ k, A none k * A k (some (V, c)) + A none (some (V, c))) =
      ∑ c : ZMod 7, ((if (none : W) = some (V, c) then (12 : ℤ) else 0) + 2) :=
    Finset.sum_congr rfl (fun c _ => hA.sq _ _)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at h
  have e1 : ∀ k : W, ∑ c, A none k * A k (some (V, c)) = A none k * ∑ c, A k (some (V, c)) :=
    fun k => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun k _ => e1 k), sum_W, hA.diag] at h
  simp only [hA.col_sum] at h
  have e2 : ∀ W' : Fin 14, ∑ b, A none (some (W', b)) * bq A W' V = 7 * (tq A W' * bq A W' V) :=
    fun W' => by
      rw [Finset.sum_congr rfl (fun b _ => by rw [hA.tx W' b]), Finset.sum_const, Finset.card_univ,
        ZMod.card, nsmul_eq_mul]
      unfold tq; push_cast; ring
  rw [Finset.sum_congr rfl (fun W' _ => e2 W'), ← Finset.mul_sum] at h
  simp at h
  linarith

theorem qdata : QData (tq A) (bq A) where
  t01 := hA.tq01
  nonneg := hA.bq_nonneg
  symm := hA.bq_symm
  row := hA.bq_row
  tsum := hA.tq_sum
  sq := hA.bq_sq
  xrow := hA.xrow
  even := hA.bq_even

end Setting

end Conway7
