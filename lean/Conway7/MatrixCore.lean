import Conway7.Gen.Census

/-!
# The core matrix theorem

There is no symmetric nonnegative integral `12 × 12` matrix `C` with zero diagonal such that
`C 1 = 12·1`, `C u = 0` and `C² + C = 12 I + 12 J - 2 u uᵀ` (`u = (1³, (-1)³, 0⁶)`).

The `LL` block `P` and the `RR` block `Q` are first brought to canonical form by transpositions
inside `{0,1,2}` and inside `{3,4,5}` (these preserve `u`); the generated census lemmas then
treat the six canonical pairs.
-/

open Matrix Finset

namespace Conway7

variable {C : Matrix (Fin 12) (Fin 12) ℤ}

/-- Evaluate an entry of a relabelled matrix and close it from the hypotheses (up to symmetry). -/
macro "swapfact" hC:term : tactic =>
  `(tactic| (simp only [Equiv.swap_apply_def]; simp only [Fin.reduceEq, ite_true, ite_false]; first | assumption | (rw [($hC).symm]; assumption)))

theorem reduceQ_111 (hC : IsOrbitMatrix C) (h01 : C 0 1 = 1) (h02 : C 0 2 = 1)
    (h12 : C 1 2 = 1) : False := by
  have hq := hC.hQ_eq
  have b1 := hC.B_pos34; have b2 := hC.B_pos35; have b3 := hC.B_pos45
  exact census_111_111 hC h01 h02 h12 (by omega) (by omega) (by omega)

theorem reduceQ_112 (hC : IsOrbitMatrix C) (h01 : C 0 1 = 1) (h02 : C 0 2 = 1)
    (h12 : C 1 2 = 2) : False := by
  have hq := hC.hQ_eq
  have b1 := hC.B_pos34; have b2 := hC.B_pos35; have b3 := hC.B_pos45
  rcases (show (C 3 4 = 1 ∧ C 3 5 = 1 ∧ C 4 5 = 2) ∨ (C 3 4 = 1 ∧ C 3 5 = 2 ∧ C 4 5 = 1) ∨
      (C 3 4 = 2 ∧ C 3 5 = 1 ∧ C 4 5 = 1) by omega) with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact census_112_112 hC h01 h02 h12 a b c
  · exact census_112_112 (hC.perm (Equiv.swap 3 4) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact census_112_112 (hC.perm (Equiv.swap 3 5) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)

theorem reduceQ_113 (hC : IsOrbitMatrix C) (h01 : C 0 1 = 1) (h02 : C 0 2 = 1)
    (h12 : C 1 2 = 3) : False := by
  have hq := hC.hQ_eq
  have b1 := hC.B_pos34; have b2 := hC.B_pos35; have b3 := hC.B_pos45
  rcases (show (C 3 4 = 1 ∧ C 3 5 = 1 ∧ C 4 5 = 3) ∨ (C 3 4 = 1 ∧ C 3 5 = 3 ∧ C 4 5 = 1) ∨
      (C 3 4 = 3 ∧ C 3 5 = 1 ∧ C 4 5 = 1) ∨ (C 3 4 = 1 ∧ C 3 5 = 2 ∧ C 4 5 = 2) ∨
      (C 3 4 = 2 ∧ C 3 5 = 1 ∧ C 4 5 = 2) ∨ (C 3 4 = 2 ∧ C 3 5 = 2 ∧ C 4 5 = 1) by omega)
    with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact census_113_113 hC h01 h02 h12 a b c
  · exact census_113_113 (hC.perm (Equiv.swap 3 4) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact census_113_113 (hC.perm (Equiv.swap 3 5) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact census_113_122 hC h01 h02 h12 a b c
  · exact census_113_122 (hC.perm (Equiv.swap 4 5) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact census_113_122 (hC.perm (Equiv.swap 3 5) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)

theorem reduceQ_122 (hC : IsOrbitMatrix C) (h01 : C 0 1 = 1) (h02 : C 0 2 = 2)
    (h12 : C 1 2 = 2) : False := by
  have hq := hC.hQ_eq
  have b1 := hC.B_pos34; have b2 := hC.B_pos35; have b3 := hC.B_pos45
  rcases (show (C 3 4 = 1 ∧ C 3 5 = 1 ∧ C 4 5 = 3) ∨ (C 3 4 = 1 ∧ C 3 5 = 3 ∧ C 4 5 = 1) ∨
      (C 3 4 = 3 ∧ C 3 5 = 1 ∧ C 4 5 = 1) ∨ (C 3 4 = 1 ∧ C 3 5 = 2 ∧ C 4 5 = 2) ∨
      (C 3 4 = 2 ∧ C 3 5 = 1 ∧ C 4 5 = 2) ∨ (C 3 4 = 2 ∧ C 3 5 = 2 ∧ C 4 5 = 1) by omega)
    with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact census_122_113 hC h01 h02 h12 a b c
  · exact census_122_113 (hC.perm (Equiv.swap 3 4) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact census_122_113 (hC.perm (Equiv.swap 3 5) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact census_122_122 hC h01 h02 h12 a b c
  · exact census_122_122 (hC.perm (Equiv.swap 4 5) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact census_122_122 (hC.perm (Equiv.swap 3 5) (by decide))
      (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)

/-- **Core theorem.** No exterior quotient matrix with zero diagonal exists. -/
theorem no_orbit_matrix (C : Matrix (Fin 12) (Fin 12) ℤ) : ¬ IsOrbitMatrix C := by
  intro hC
  have p1 := hC.A_pos01; have p2 := hC.A_pos02; have p3 := hC.A_pos12
  have hge := hC.h_ge; have hle := hC.h_le
  rcases (show (C 0 1 = 1 ∧ C 0 2 = 1 ∧ C 1 2 = 1) ∨
      (C 0 1 = 1 ∧ C 0 2 = 1 ∧ C 1 2 = 2) ∨ (C 0 1 = 1 ∧ C 0 2 = 2 ∧ C 1 2 = 1) ∨
      (C 0 1 = 2 ∧ C 0 2 = 1 ∧ C 1 2 = 1) ∨
      (C 0 1 = 1 ∧ C 0 2 = 1 ∧ C 1 2 = 3) ∨ (C 0 1 = 1 ∧ C 0 2 = 3 ∧ C 1 2 = 1) ∨
      (C 0 1 = 3 ∧ C 0 2 = 1 ∧ C 1 2 = 1) ∨
      (C 0 1 = 1 ∧ C 0 2 = 2 ∧ C 1 2 = 2) ∨ (C 0 1 = 2 ∧ C 0 2 = 1 ∧ C 1 2 = 2) ∨
      (C 0 1 = 2 ∧ C 0 2 = 2 ∧ C 1 2 = 1) by omega)
    with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ |
      ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact reduceQ_111 hC a b c
  · exact reduceQ_112 hC a b c
  · exact reduceQ_112 (hC.perm (Equiv.swap 0 1) (by decide)) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact reduceQ_112 (hC.perm (Equiv.swap 0 2) (by decide)) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact reduceQ_113 hC a b c
  · exact reduceQ_113 (hC.perm (Equiv.swap 0 1) (by decide)) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact reduceQ_113 (hC.perm (Equiv.swap 0 2) (by decide)) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact reduceQ_122 hC a b c
  · exact reduceQ_122 (hC.perm (Equiv.swap 1 2) (by decide)) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)
  · exact reduceQ_122 (hC.perm (Equiv.swap 0 2) (by decide)) (by swapfact hC) (by swapfact hC)
      (by swapfact hC)

end Conway7
