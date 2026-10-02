import Conway7.Graph

/-!
# Main theorem

**Theorem.** A strongly regular graph with parameters `(99, 14, 1, 2)` has no automorphism of
order 7: every automorphism `σ` with `σ^[7] = id` is the identity.

The fixed vertex `x` is unique (`unique_fixed`); the other 98 vertices are relabelled as
`Fin 14 × ZMod 7` with `σ` acting as the shift, and the adjacency matrix in these coordinates
satisfies `Setting`, which is contradictory (`Setting.false`).
-/

open Finset Matrix

namespace Conway7

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `A² + A = 12 I + 2 J` for the adjacency matrix of an `srg(99,14,1,2)`. -/
theorem adj_sq {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2) (i j : V) :
    ∑ k, G.adjMatrix ℤ i k * G.adjMatrix ℤ k j + G.adjMatrix ℤ i j =
      (if i = j then 12 else 0) + 2 := by
  have hAA : G.adjMatrix ℤ * G.adjMatrix ℤ + G.adjMatrix ℤ =
      (12 : ℤ) • (1 : Matrix V V ℤ) + (2 : ℤ) • Matrix.of (fun _ _ => 1) := by
    have h := hG.matrix_eq (α := ℤ)
    rw [sq] at h
    ext v w
    have hvw := congrFun (congrFun h v) w
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.smul_apply] at hvw
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.of_apply,
      hvw]
    simp only [Matrix.one_apply, SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
      smul_eq_mul, nsmul_eq_mul]
    by_cases hvw' : v = w
    · subst hvw'
      simp
    · by_cases hadj : G.Adj v w <;> simp [hvw', hadj]
  have h := congrFun (congrFun hAA i) j
  rw [Matrix.add_apply, Matrix.mul_apply] at h
  rw [h]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> ring

theorem no_order7_aux (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2)
    (σ : G ≃g G) (h7 : ∀ v, (⇑σ)^[7] v = v) (hne : ∃ v, σ v ≠ v) : False := by
  classical
  obtain ⟨x, hx, hux⟩ := unique_fixed hG σ h7 hne
  -- `σ` on the other vertices
  have hmem : ∀ v, v ≠ x ↔ σ v ≠ x := by
    intro v
    constructor
    · intro hv h; apply hv; rw [← hx] at h; exact σ.injective h
    · intro hv h; apply hv; rw [h, hx]
  let τ : {v // v ≠ x} ≃ {v // v ≠ x} :=
    Equiv.subtypeEquiv (p := fun v => v ≠ x) (q := fun v => v ≠ x) σ.toEquiv hmem
  have hτi : ∀ (n : ℕ) (w : {v // v ≠ x}), (τ^[n] w).1 = (⇑σ)^[n] w.1 := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]; rfl
  have hτ7 : ∀ w, τ^[7] w = w := fun w => Subtype.ext (by rw [hτi]; exact h7 w.1)
  have hτfree : ∀ w, τ w ≠ w := by
    intro w h
    exact w.2 (hux w.1 (congrArg Subtype.val h))
  obtain ⟨m, e1, he1⟩ := exists_relabel_free hτ7 hτfree
  have hm : m = 14 := by
    have h := Fintype.card_congr e1
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card, Fintype.card_subtype_compl,
      hG.card, Fintype.card_unique] at h
    omega
  subst hm
  let e : W ≃ V := (Equiv.optionCongr e1).trans (Equiv.optionSubtypeNe x)
  have e_none : e none = x := rfl
  have e_some : ∀ p, e (some p) = (e1 p).1 := fun p => rfl
  have he : ∀ w, σ (e w) = e (sh w) := by
    intro w
    rcases w with _ | ⟨U, b⟩
    · rw [e_none, hx]; rfl
    · rw [e_some]
      simp only [sh]
      rw [e_some, he1]
      rfl
  let A : Matrix W W ℤ := (G.adjMatrix ℤ).submatrix e e
  have hA : Setting A := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      simp only [A, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]
    · intro i j
      simp only [A, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
      split_ifs <;> simp
    · intro i
      simp [A]
    · intro i j
      have h := adj_sq hG (e i) (e j)
      simp only [A, Matrix.submatrix_apply]
      have hs : ∑ k, G.adjMatrix ℤ (e i) (e k) * G.adjMatrix ℤ (e k) (e j) =
          ∑ k, G.adjMatrix ℤ (e i) k * G.adjMatrix ℤ k (e j) :=
        Equiv.sum_comp e (fun k => G.adjMatrix ℤ (e i) k * G.adjMatrix ℤ k (e j))
      rw [hs, h]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, e.injective.ne hij]
    · intro U V' b c
      simp only [A, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
      have h1 : e (some (U, b + 1)) = σ (e (some (U, b))) := by rw [he]; rfl
      have h2 : e (some (V', c + 1)) = σ (e (some (V', c))) := by rw [he]; rfl
      rw [h1, h2]
      simp only [σ.map_adj_iff]
    · intro U b
      simp only [A, Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
      have h1 : e (some (U, b + 1)) = σ (e (some (U, b))) := by rw [he]; rfl
      rw [h1, e_none]
      have hσ := σ.map_adj_iff (v := x) (w := e (some (U, b)))
      rw [hx] at hσ
      simp only [hσ]
  exact hA.false

/-- **Main theorem.** An automorphism `σ` of an `srg(99,14,1,2)` with `σ^[7] = id` is the
identity. -/
theorem no_order7 (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsSRGWith 99 14 1 2)
    (σ : G ≃g G) (h7 : ∀ v, (⇑σ)^[7] v = v) : ∀ v, σ v = v := by
  by_contra hne
  push_neg at hne
  exact no_order7_aux G hG σ h7 hne

end Conway7
