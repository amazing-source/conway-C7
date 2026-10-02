import Conway7.Final
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.OrderOfElement

/-!
# Proofs of the statements of `Challenge.lean`

Same names and same statements as `Challenge.lean`; `lake comparator` checks that the statements
are identical. Everything follows from `Conway7.no_order7` (`Conway7/Final.lean`):

* the group forms: `σ ^ 7 = 1` means `σ^[7] v = v` for every `v`, then Cauchy's theorem;
* the elementary form: a symmetric Boolean matrix with zero diagonal is a `SimpleGraph`, the
  counting hypotheses are `IsSRGWith`, and a map with `σ^[7] = id` preserving adjacency is an
  automorphism;
* the sanity checks: the triangular graph `T(7)` and the rotation `i ↦ i + 1` of `{0, …, 6}`,
  facts checked by `decide`.
-/

namespace Conway99

/-- For an automorphism, `σ ^ n` is the `n`-th iterate. -/
theorem pow_apply_iter {V : Type*} {G : SimpleGraph V} (σ : G ≃g G) (n : ℕ) (v : V) :
    (σ ^ n) v = (⇑σ)^[n] v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [pow_succ, RelIso.mul_apply, ih, Function.iterate_succ_apply]

theorem srg99_aut_pow_seven {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h7 : σ ^ 7 = 1) : σ = 1 := by
  classical
  have hit : ∀ v, (⇑σ)^[7] v = v := fun v => by rw [← pow_apply_iter, h7, RelIso.one_apply]
  exact RelIso.ext fun v => by rw [RelIso.one_apply]; exact Conway7.no_order7 G hG σ hit v

theorem srg99_no_orderOf_seven {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) : orderOf σ ≠ 7 := by
  intro h
  have h7 : σ ^ 7 = 1 := h ▸ pow_orderOf_eq_one σ
  have hid := srg99_aut_pow_seven G hG σ h7
  rw [hid, orderOf_one] at h
  omega

/-- The automorphisms of a finite graph form a finite type. -/
theorem finite_aut {V : Type*} [Finite V] (G : SimpleGraph V) : Finite (G ≃g G) :=
  Finite.of_injective _ RelIso.toEquiv_injective

theorem srg99_seven_not_dvd_card_aut {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) : ¬ 7 ∣ Nat.card (G ≃g G) := by
  intro hdvd
  have := finite_aut G
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 7 hdvd
  exact srg99_no_orderOf_seven G hG σ hσ

/-! ### From a Boolean adjacency matrix to Mathlib's graphs -/

/-- The simple graph whose adjacency matrix is `adj`. -/
def graphOf {n : ℕ} (adj : Fin n → Fin n → Bool) (h_symm : ∀ i j, adj i j = adj j i)
    (h_loop : ∀ i, adj i i = false) : SimpleGraph (Fin n) where
  Adj i j := adj i j = true
  symm := ⟨fun i j h => (h_symm j i).trans h⟩
  loopless := ⟨fun i h => by rw [h_loop i] at h; exact Bool.false_ne_true h⟩

instance {n : ℕ} (adj : Fin n → Fin n → Bool) (h_symm : ∀ i j, adj i j = adj j i)
    (h_loop : ∀ i, adj i i = false) : DecidableRel (graphOf adj h_symm h_loop).Adj :=
  fun i j => inferInstanceAs (Decidable (adj i j = true))

/-- Counting with `List.countP` over `[0, …, n - 1]` is the cardinality of a `Finset` filter. -/
theorem card_filter_eq_countP {n : ℕ} (p : Fin n → Bool) :
    (Finset.univ.filter (fun i => p i = true)).card = (List.finRange n).countP p := by
  rw [Fin.univ_def, List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter]

/-- The counting hypotheses say that `graphOf adj` is strongly regular. -/
theorem graphOf_isSRGWith {n k l m : ℕ} (adj : Fin n → Fin n → Bool)
    (h_symm : ∀ i j, adj i j = adj j i) (h_loop : ∀ i, adj i i = false)
    (h_deg : ∀ i, (List.finRange n).countP (fun j => adj i j) = k)
    (h_adj : ∀ i j, adj i j = true →
      (List.finRange n).countP (fun x => adj i x && adj j x) = l)
    (h_nonadj : ∀ i j, i ≠ j → adj i j = false →
      (List.finRange n).countP (fun x => adj i x && adj j x) = m) :
    (graphOf adj h_symm h_loop).IsSRGWith n k l m where
  card := Fintype.card_fin n
  regular i := by
    rw [← h_deg i, ← card_filter_eq_countP, SimpleGraph.degree,
      SimpleGraph.neighborFinset_eq_filter]
    rfl
  of_adj i j h := by
    rw [← h_adj i j h, ← card_filter_eq_countP, ← Set.toFinset_card]
    congr 1
    ext x
    simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true]
    exact Iff.rfl
  of_not_adj := by
    intro i j hne h
    have h' : adj i j = false := by simpa [graphOf] using h
    rw [← h_nonadj i j hne h', ← card_filter_eq_countP, ← Set.toFinset_card]
    congr 1
    ext x
    simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, Finset.mem_filter,
      Finset.mem_univ, true_and, Bool.and_eq_true]
    exact Iff.rfl

/-- A map with `σ^[7] = id` that preserves `adj` is an automorphism of `graphOf adj`. -/
def autOf {n : ℕ} {adj : Fin n → Fin n → Bool} {h_symm : ∀ i j, adj i j = adj j i}
    {h_loop : ∀ i, adj i i = false} (σ : Fin n → Fin n)
    (h_aut : ∀ i j, adj (σ i) (σ j) = adj i j) (h_pow : ∀ i, σ^[7] i = i) :
    graphOf adj h_symm h_loop ≃g graphOf adj h_symm h_loop where
  toFun := σ
  invFun i := σ^[6] i
  left_inv i := by
    change σ^[6] (σ i) = i
    rw [← Function.iterate_succ_apply]; exact h_pow i
  right_inv i := by
    change σ (σ^[6] i) = i
    rw [← Function.iterate_succ_apply' σ 6 i]; exact h_pow i
  map_rel_iff' := by
    intro a b
    simp only [graphOf, Equiv.coe_fn_mk, h_aut]

theorem srg99_elementary (adj : Fin 99 → Fin 99 → Bool)
    (h_symm : ∀ i j, adj i j = adj j i)
    (h_loop : ∀ i, adj i i = false)
    (h_deg : ∀ i, (List.finRange 99).countP (fun j => adj i j) = 14)
    (h_adj : ∀ i j, adj i j = true →
      (List.finRange 99).countP (fun k => adj i k && adj j k) = 1)
    (h_nonadj : ∀ i j, i ≠ j → adj i j = false →
      (List.finRange 99).countP (fun k => adj i k && adj j k) = 2)
    (σ : Fin 99 → Fin 99)
    (h_aut : ∀ i j, adj (σ i) (σ j) = adj i j)
    (h_pow : ∀ i, σ^[7] i = i) :
    ∀ i, σ i = i :=
  Conway7.no_order7 (graphOf adj h_symm h_loop)
    (graphOf_isSRGWith adj h_symm h_loop h_deg h_adj h_nonadj) (autOf σ h_aut h_pow) h_pow

/-! ### Sanity checks: the triangular graph `T(7)` -/

/-- The 21 two-element subsets of `{0, …, 6}`, in lexicographic order. -/
def pairs7 : Fin 21 → Fin 7 × Fin 7 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3),
    (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]

/-- The triangular graph `T(7)`: two pairs are adjacent when they share exactly one element.
It is an srg(21, 10, 5, 4). -/
def tri7 (i j : Fin 21) : Bool :=
  i != j && ((pairs7 i).1 == (pairs7 j).1 || (pairs7 i).1 == (pairs7 j).2 ||
    (pairs7 i).2 == (pairs7 j).1 || (pairs7 i).2 == (pairs7 j).2)

/-- The rotation `a ↦ a + 1` of `{0, …, 6}`, acting on the pairs: an automorphism of order 7. -/
def rot7 : Fin 21 → Fin 21 :=
  ![6, 7, 8, 9, 10, 0, 11, 12, 13, 14, 1, 15, 16, 17, 2, 18, 19, 3, 20, 4, 5]

theorem tri7_symm : ∀ i j, tri7 i j = tri7 j i := by decide
theorem tri7_loop : ∀ i, tri7 i i = false := by decide
theorem tri7_deg : ∀ i, (List.finRange 21).countP (fun j => tri7 i j) = 10 := by decide +kernel
theorem tri7_adj : ∀ i j, tri7 i j = true →
    (List.finRange 21).countP (fun k => tri7 i k && tri7 j k) = 5 := by decide +kernel
theorem tri7_nonadj : ∀ i j, i ≠ j → tri7 i j = false →
    (List.finRange 21).countP (fun k => tri7 i k && tri7 j k) = 4 := by decide +kernel
theorem rot7_aut : ∀ i j, tri7 (rot7 i) (rot7 j) = tri7 i j := by decide +kernel
theorem rot7_pow : ∀ i, rot7^[7] i = i := by decide
theorem rot7_ne : rot7 0 ≠ 0 := by decide

/-- `T(7)` as a `SimpleGraph`. -/
def triGraph : SimpleGraph (Fin 21) := graphOf tri7 tri7_symm tri7_loop

instance : DecidableRel triGraph.Adj :=
  inferInstanceAs (DecidableRel (graphOf tri7 tri7_symm tri7_loop).Adj)

theorem triGraph_srg : triGraph.IsSRGWith 21 10 5 4 :=
  graphOf_isSRGWith tri7 tri7_symm tri7_loop tri7_deg tri7_adj tri7_nonadj

/-- The rotation as an automorphism of `T(7)`. -/
def rotAut : triGraph ≃g triGraph := autOf rot7 rot7_aut rot7_pow

theorem rotAut_pow7 : rotAut ^ 7 = 1 :=
  RelIso.ext fun i => by rw [pow_apply_iter, RelIso.one_apply]; exact rot7_pow i

theorem srg21_aut_pow_seven_false :
    ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsSRGWith 21 10 5 4 → ∀ σ : G ≃g G, σ ^ 7 = 1 → σ = 1 :=
  fun h => rot7_ne (congrArg (fun τ : triGraph ≃g triGraph => τ 0)
    (h triGraph triGraph_srg rotAut rotAut_pow7))

theorem srg21_group_forms_false :
    ∃ (G : SimpleGraph (Fin 21)) (_ : DecidableRel G.Adj), G.IsSRGWith 21 10 5 4 ∧
      (∃ σ : G ≃g G, orderOf σ = 7) ∧ 7 ∣ Nat.card (G ≃g G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hσ : orderOf rotAut = 7 := by
    apply orderOf_eq_prime rotAut_pow7
    intro h
    apply rot7_ne
    exact congrArg (fun τ : triGraph ≃g triGraph => τ 0) h
  have := finite_aut triGraph
  exact ⟨triGraph, inferInstance, triGraph_srg, ⟨rotAut, hσ⟩, hσ ▸ orderOf_dvd_natCard rotAut⟩

theorem srg21_elementary_false :
    ¬ ∀ (adj : Fin 21 → Fin 21 → Bool),
      (∀ i j, adj i j = adj j i) →
      (∀ i, adj i i = false) →
      (∀ i, (List.finRange 21).countP (fun j => adj i j) = 10) →
      (∀ i j, adj i j = true → (List.finRange 21).countP (fun k => adj i k && adj j k) = 5) →
      (∀ i j, i ≠ j → adj i j = false →
        (List.finRange 21).countP (fun k => adj i k && adj j k) = 4) →
      ∀ σ : Fin 21 → Fin 21, (∀ i j, adj (σ i) (σ j) = adj i j) → (∀ i, σ^[7] i = i) →
        ∀ i, σ i = i :=
  fun h => rot7_ne (h tri7 tri7_symm tri7_loop tri7_deg tri7_adj tri7_nonadj rot7 rot7_aut
    rot7_pow 0)

end Conway99
