import Conway7.Reindex
import Conway7.Spectral
import Conway7.MatrixCore

/-!
# The relabelled adjacency matrix cannot exist

`Setting A` (a shift-invariant `srg(99,14,1,2)` adjacency matrix on `Option (Fin 14 × ZMod 7)`)
leads to a contradiction:

* `QData.exists_C` builds the exterior matrix `C` (paper, Section 4);
* the spectral step gives `7 d = tr C + 42` and `54 = d + 6 k`, while `0 ≤ tr C ≤ 39`, so
  `d = 6` and `C` has zero diagonal (paper, Section 5);
* `no_orbit_matrix` (paper, Sections 6–8) excludes `C`.
-/

open Finset

namespace Conway7

variable {A : Matrix W W ℤ}

theorem Setting.false (hA : Setting A) : False := by
  have hq := hA.qdata
  obtain ⟨C, hC, L, hLL, hdiag⟩ := hq.exists_C
  obtain ⟨d, k, hd, hk⟩ := hA.spectral
  have hnn : ∀ U, 0 ≤ bq A U U := fun U => hq.nonneg U U
  have hge : 0 ≤ ∑ U, bq A U U := Finset.sum_nonneg (fun U _ => hnn U)
  have hle : ∑ U, bq A U U ≤ 39 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L), hLL, zero_add]
    calc ∑ U ∈ Finset.univ.erase L, bq A U U ≤ ∑ U ∈ Finset.univ.erase L, (3 : ℤ) :=
          Finset.sum_le_sum (fun U _ => hq.diag_le3 U)
      _ = 39 := by simp [Finset.card_erase_of_mem]
  have hz : ∑ U, bq A U U = 0 := by omega
  have hall : ∀ U, bq A U U = 0 := fun U =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun V _ => hnn V)).mp hz U (Finset.mem_univ U)
  exact no_orbit_matrix C (hC.toIsOrbitMatrix (hdiag hall))

end Conway7
