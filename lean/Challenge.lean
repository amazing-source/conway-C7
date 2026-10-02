import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.OrderOfElement

/-!
# The statement, and nothing else

This is the only file a reader has to trust. It imports Mathlib and nothing from this project, and
it contains no definition: every notion used below comes from Lean's core library or from Mathlib.
All proofs here are `sorry`.

The proofs are in `Solution.lean`. `lake comparator` (configuration: `comparator.json`) checks that
every theorem there has exactly the statement written here (the same Lean term, and every definition
it depends on identical), that the proofs use no axiom besides `propext`, `Quot.sound` and
`Classical.choice`, and that the kernel accepts them.

* `srg99_aut_pow_seven`: the graph form, with Mathlib's `SimpleGraph.IsSRGWith` and the group
  `G ≃g G` of automorphisms: an automorphism `σ` with `σ ^ 7 = 1` is the identity;
* `srg99_no_orderOf_seven`, `srg99_seven_not_dvd_card_aut`: the group forms;
* `srg99_elementary`: the same statement with no graph library at all: the vertices are
  `0, …, 98`, adjacency is a Boolean matrix, and counting is `List.countP` from Lean's core;
* `srg21_*`: sanity checks. The same formulas with `(21, 10, 5, 4)` in place of `(99, 14, 1, 2)`
  are false, because the triangular graph `T(7)` (the line graph of `K₇`) is an
  srg(21, 10, 5, 4) with an automorphism of order 7. So the hypotheses can be met and the
  conclusions can fail: the statements are not true for a trivial reason.
-/

namespace Conway99

/-- An automorphism `σ` of a strongly regular graph with parameters `(99, 14, 1, 2)` such that
`σ ^ 7 = 1` is the identity. -/
theorem srg99_aut_pow_seven {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h7 : σ ^ 7 = 1) : σ = 1 := by
  sorry

/-- The automorphism group of a strongly regular graph with parameters `(99, 14, 1, 2)` has no
element of order 7. -/
theorem srg99_no_orderOf_seven {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) : orderOf σ ≠ 7 := by
  sorry

/-- The order of the automorphism group of a strongly regular graph with parameters
`(99, 14, 1, 2)` is not divisible by 7. -/
theorem srg99_seven_not_dvd_card_aut {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) : ¬ 7 ∣ Nat.card (G ≃g G) := by
  sorry

/-- `srg99_aut_pow_seven` without any graph library. The vertices are `0, …, 98` (the type
`Fin 99`) and `adj i j` says whether `i` and `j` are adjacent. The five hypotheses on `adj` say that
it is the adjacency matrix of an srg(99, 14, 1, 2): it is symmetric with zero diagonal, every vertex
has 14 neighbours, two adjacent vertices have exactly 1 common neighbour, and two distinct
non-adjacent vertices have exactly 2 common neighbours. The map `σ` preserves adjacency and
non-adjacency, and its seventh iterate is the identity (so `σ` is a bijection: an automorphism of
order 1 or 7). Conclusion: `σ` is the identity. -/
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
    ∀ i, σ i = i := by
  sorry

/-! ### Sanity checks: the same formulas are false for srg(21, 10, 5, 4) -/

/-- `srg99_aut_pow_seven` with `(21, 10, 5, 4)` in place of `(99, 14, 1, 2)` is false. -/
theorem srg21_aut_pow_seven_false :
    ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsSRGWith 21 10 5 4 → ∀ σ : G ≃g G, σ ^ 7 = 1 → σ = 1 := by
  sorry

/-- The group forms with `(21, 10, 5, 4)` in place of `(99, 14, 1, 2)` are false: some
srg(21, 10, 5, 4) has an automorphism of order 7, and 7 divides the order of its automorphism
group. -/
theorem srg21_group_forms_false :
    ∃ (G : SimpleGraph (Fin 21)) (_ : DecidableRel G.Adj), G.IsSRGWith 21 10 5 4 ∧
      (∃ σ : G ≃g G, orderOf σ = 7) ∧ 7 ∣ Nat.card (G ≃g G) := by
  sorry

/-- `srg99_elementary` with `(21, 10, 5, 4)` in place of `(99, 14, 1, 2)` is false. -/
theorem srg21_elementary_false :
    ¬ ∀ (adj : Fin 21 → Fin 21 → Bool),
      (∀ i j, adj i j = adj j i) →
      (∀ i, adj i i = false) →
      (∀ i, (List.finRange 21).countP (fun j => adj i j) = 10) →
      (∀ i j, adj i j = true → (List.finRange 21).countP (fun k => adj i k && adj j k) = 5) →
      (∀ i j, i ≠ j → adj i j = false →
        (List.finRange 21).countP (fun k => adj i k && adj j k) = 4) →
      ∀ σ : Fin 21 → Fin 21, (∀ i j, adj (σ i) (σ j) = adj i j) → (∀ i, σ^[7] i = i) →
        ∀ i, σ i = i := by
  sorry

end Conway99
