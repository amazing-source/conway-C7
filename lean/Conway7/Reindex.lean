import Conway7.Quotient
import Conway7.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic

/-!
# From the quotient data to the exterior matrix `C`

Given `QData t bm` (orbit counts on the 14 orbits of size 7), the orbits with `t = 1` are the two
neighbourhood orbits `L, R`, the other twelve are the exterior orbits. With `u U = bm U L - 1` we
order the exterior orbits so that `u = (1,1,1,-1,-1,-1,0,…,0)` and obtain a matrix `C` satisfying
all the hypotheses of `IsOrbitMatrix` except, for now, the zero diagonal (paper, Section 4).
-/

open Finset Matrix

namespace Conway7

/-- `IsOrbitMatrix` without the zero diagonal -/
structure PreOrbit (C : Matrix (Fin 12) (Fin 12) ℤ) : Prop where
  symm : ∀ i j, C i j = C j i
  nonneg : ∀ i j, 0 ≤ C i j
  row : ∀ i, ∑ j, C i j = 12
  usum : ∀ i, ∑ j, C i j * u j = 0
  sq : ∀ i j, ∑ k, C i k * C k j + C i j = (if i = j then 12 else 0) + 12 - 2 * (u i * u j)

lemma PreOrbit.toIsOrbitMatrix {C : Matrix (Fin 12) (Fin 12) ℤ} (h : PreOrbit C)
    (hd : ∀ i, C i i = 0) : IsOrbitMatrix C :=
  ⟨h.symm, h.nonneg, hd, h.row, h.usum, h.sq⟩

lemma u_eq (i : Fin 12) : u i = if i.val < 3 then 1 else if i.val < 6 then -1 else 0 := by
  fin_cases i <;> rfl

/-- Ordering the exterior orbits by the value of `u`. -/
lemma exists_reindex (ext : Finset (Fin 14)) (hcard : ext.card = 12) (uv : Fin 14 → ℤ)
    (h01 : ∀ U ∈ ext, uv U = 1 ∨ uv U = -1 ∨ uv U = 0) (hs : ∑ U ∈ ext, uv U = 0)
    (hs2 : ∑ U ∈ ext, uv U * uv U = 6) :
    ∃ e : Fin 12 → Fin 14, Function.Injective e ∧ (∀ i, e i ∈ ext) ∧ ∀ i, uv (e i) = u i := by
  classical
  set S1 := ext.filter (fun U => uv U = 1)
  set S2 := ext.filter (fun U => uv U = -1)
  set S3 := ext.filter (fun U => uv U = 0)
  have e1 : ∑ U ∈ ext, uv U = (S1.card : ℤ) - S2.card := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun U hU => ?_)
    rcases h01 U hU with h | h | h <;> simp [h]
  have e2 : ∑ U ∈ ext, uv U * uv U = (S1.card : ℤ) + S2.card := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun U hU => ?_)
    rcases h01 U hU with h | h | h <;> simp [h]
  have e3 : (ext.card : ℤ) = (S1.card : ℤ) + S2.card + S3.card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones]
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun U hU => ?_)
    rcases h01 U hU with h | h | h <;> simp [h]
  have c1 : S1.card = 3 := by omega
  have c2 : S2.card = 3 := by omega
  have c3 : S3.card = 6 := by omega
  let f1 := S1.orderEmbOfFin c1
  let f2 := S2.orderEmbOfFin c2
  let f3 := S3.orderEmbOfFin c3
  let e : Fin 12 → Fin 14 := fun i =>
    if h : i.val < 3 then f1 ⟨i.val, h⟩
    else if h' : i.val < 6 then f2 ⟨i.val - 3, by omega⟩
    else f3 ⟨i.val - 6, by omega⟩
  have m1 : ∀ k, f1 k ∈ S1 := fun k => S1.orderEmbOfFin_mem c1 k
  have m2 : ∀ k, f2 k ∈ S2 := fun k => S2.orderEmbOfFin_mem c2 k
  have m3 : ∀ k, f3 k ∈ S3 := fun k => S3.orderEmbOfFin_mem c3 k
  have hval : ∀ i, uv (e i) = u i := by
    intro i
    rw [u_eq]
    simp only [e]
    split_ifs with h h'
    · exact (Finset.mem_filter.mp (m1 _)).2
    · exact (Finset.mem_filter.mp (m2 _)).2
    · exact (Finset.mem_filter.mp (m3 _)).2
  have hmem : ∀ i, e i ∈ ext := by
    intro i
    simp only [e]
    split_ifs with h h'
    · exact (Finset.mem_filter.mp (m1 _)).1
    · exact (Finset.mem_filter.mp (m2 _)).1
    · exact (Finset.mem_filter.mp (m3 _)).1
  refine ⟨e, ?_, hmem, hval⟩
  intro i j hij
  have hu : u i = u j := by rw [← hval i, ← hval j, hij]
  rw [u_eq, u_eq] at hu
  simp only [e] at hij
  apply Fin.ext
  split_ifs at hij hu with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    first
    | (have := f1.injective hij; simp [Fin.ext_iff] at this; omega)
    | (have := f2.injective hij; simp [Fin.ext_iff] at this; omega)
    | (have := f3.injective hij; simp [Fin.ext_iff] at this; omega)
    | (norm_num at hu)

variable {t : Fin 14 → ℤ} {bm : Matrix (Fin 14) (Fin 14) ℤ}

/-- sums against `t` only see the two orbits with `t = 1` -/
lemma sum_t {L R : Fin 14} (hLR : L ≠ R) (ht : ∀ U, t U = if U = L ∨ U = R then 1 else 0)
    (f : Fin 14 → ℤ) : ∑ U, t U * f U = f L + f R := by
  rw [Finset.sum_congr rfl (fun U _ => by rw [ht U])]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [show Finset.univ.filter (fun U => U = L ∨ U = R) = {L, R} by ext; simp]
  rw [Finset.sum_pair hLR]

namespace QData

variable (hq : QData t bm)
include hq

lemma diag_le3 (U : Fin 14) : bm U U ≤ 3 := by
  have h1 := hq.sq U U
  have h2 := hq.row U
  rw [if_pos rfl] at h1
  have hsplit : ∑ W, bm U W * bm W U - ∑ W, bm U W = ∑ W, bm U W * (bm U W - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun W _ => ?_)
    rw [hq.symm W U]; ring
  have hge : bm U U * (bm U U - 1) ≤ ∑ W, bm U W * (bm U W - 1) := by
    apply Finset.single_le_sum (f := fun W => bm U W * (bm U W - 1)) _ (Finset.mem_univ U)
    intro W _
    have := hq.nonneg U W
    rcases (show bm U W = 0 ∨ 1 ≤ bm U W by omega) with h | h
    · rw [h]; norm_num
    · nlinarith
  have ht := hq.t01 U
  have h0 := hq.nonneg U U
  rcases ht with ht | ht <;> rw [ht] at h1 h2 <;> nlinarith

end QData

/-- **Section 4 of the paper.** The quotient data produce an exterior matrix `C`. -/
theorem QData.exists_C (hq : QData t bm) :
    ∃ C : Matrix (Fin 12) (Fin 12) ℤ, PreOrbit C ∧ ∃ L : Fin 14, bm L L = 0 ∧
      ((∀ U, bm U U = 0) → ∀ i, C i i = 0) := by
  classical
  -- the two orbits adjacent to the fixed vertex
  have hcard : (Finset.univ.filter (fun U => t U = 1)).card = 2 := by
    have : ∑ U, t U = ((Finset.univ.filter (fun U => t U = 1)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast
      refine Finset.sum_congr rfl (fun U _ => ?_)
      rcases hq.t01 U with h | h <;> simp [h]
    have h2 := hq.tsum
    omega
  obtain ⟨L, R, hLR, hset⟩ := Finset.card_eq_two.mp hcard
  have ht : ∀ U, t U = if U = L ∨ U = R then 1 else 0 := by
    intro U
    have hmem : U ∈ Finset.univ.filter (fun U => t U = 1) ↔ U = L ∨ U = R := by
      rw [hset]; simp
    rw [Finset.mem_filter] at hmem
    split_ifs with h
    · exact (hmem.mpr h).2
    · rcases hq.t01 U with h' | h'
      · exact h'
      · exact absurd (hmem.mp ⟨Finset.mem_univ _, h'⟩) h
  have tL : t L = 1 := by rw [ht]; simp
  have tR : t R = 1 := by rw [ht]; simp
  -- `bm L L = bm R R = 0`, `bm L R = 1`
  have xL := hq.xrow L
  have xR := hq.xrow R
  rw [sum_t hLR ht, tL] at xL
  rw [sum_t hLR ht, tR] at xR
  have eLL := hq.even L
  have eRR := hq.even R
  have nLL := hq.nonneg L L
  have nRR := hq.nonneg R R
  have nRL := hq.nonneg R L
  have nLR := hq.nonneg L R
  have sLR := hq.symm L R
  have bLL : bm L L = 0 := by
    obtain ⟨r, hr⟩ := eLL; omega
  have bRR : bm R R = 0 := by
    obtain ⟨r, hr⟩ := eRR; omega
  have bLR : bm L R = 1 := by omega
  -- exterior orbits
  set ext := Finset.univ.filter (fun U => t U = 0)
  have hext : ∀ U, U ∈ ext ↔ U ≠ L ∧ U ≠ R := by
    intro U
    simp only [ext, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ht U]
    by_cases h : U = L ∨ U = R
    · rw [if_pos h]
      constructor
      · intro h'; exact absurd h' one_ne_zero
      · rintro ⟨h1, h2⟩; rcases h with h | h <;> contradiction
    · rw [if_neg h]
      push_neg at h
      simpa using h
  have hextcard : ext.card = 12 := by
    have : ext = (Finset.univ.erase L).erase R := by
      ext U; rw [hext]; simp [and_comm]
    rw [this, Finset.card_erase_of_mem (by simp [hLR.symm]), Finset.card_erase_of_mem (by simp)]
    simp
  have sum_split : ∀ f : Fin 14 → ℤ, ∑ U, f U = f L + f R + ∑ U ∈ ext, f U := by
    intro f
    have : ext = (Finset.univ.erase L).erase R := by
      ext U; rw [hext]; simp [and_comm]
    rw [this, Finset.sum_erase_eq_sub (by simp [hLR.symm]), Finset.sum_erase_eq_sub (by simp)]
    ring
  -- for an exterior orbit, `bm U L + bm U R = 2`
  have hUR : ∀ U ∈ ext, bm U L + bm U R = 2 := by
    intro U hU
    have := hq.xrow U
    rw [sum_t hLR ht] at this
    have h0 : t U = 0 := (Finset.mem_filter.mp hU).2
    rw [h0, hq.symm L U, hq.symm R U] at this
    linarith
  -- `u U = bm U L - 1`
  have hu01 : ∀ U ∈ ext, bm U L - 1 = 1 ∨ bm U L - 1 = -1 ∨ bm U L - 1 = 0 := by
    intro U hU
    have := hUR U hU
    have := hq.nonneg U L
    have := hq.nonneg U R
    omega
  have hrowL := hq.row L
  rw [sum_split, bLL, bLR, tL] at hrowL
  have hsqL := hq.sq L L
  rw [if_pos rfl, tL] at hsqL
  rw [sum_split] at hsqL
  rw [bLL, bLR, hq.symm R L, bLR] at hsqL
  have hs : ∑ U ∈ ext, (bm U L - 1) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hextcard]
    rw [Finset.sum_congr rfl (fun U _ => hq.symm U L)]
    simp; linarith
  have hs2 : ∑ U ∈ ext, (bm U L - 1) * (bm U L - 1) = 6 := by
    have e : ∀ U ∈ ext, (bm U L - 1) * (bm U L - 1) = bm L U * bm U L - 2 * bm L U + 1 := by
      intro U _; rw [hq.symm L U]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, hextcard]
    simp; linarith
  obtain ⟨e, he, hemem, heu⟩ := exists_reindex ext hextcard (fun U => bm U L - 1) hu01 hs hs2
  -- reindexing sums
  have himage : Finset.univ.image e = ext := by
    apply Finset.eq_of_subset_of_card_le
    · intro U hU
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hU
      exact hemem i
    · rw [Finset.card_image_of_injective _ he, hextcard]; simp
  have sum_e : ∀ f : Fin 14 → ℤ, ∑ i, f (e i) = ∑ U ∈ ext, f U := by
    intro f
    rw [← himage, Finset.sum_image (fun i _ j _ h => he h)]
  refine ⟨fun i j => bm (e i) (e j), ⟨?_, ?_, ?_, ?_, ?_⟩, L, bLL, ?_⟩
  · intro i j; exact hq.symm _ _
  · intro i j; exact hq.nonneg _ _
  · intro i
    rw [sum_e (fun U => bm (e i) U)]
    have h := hq.row (e i)
    rw [sum_split] at h
    have h0 : t (e i) = 0 := (Finset.mem_filter.mp (hemem i)).2
    have h1 := hUR (e i) (hemem i)
    linarith
  · intro i
    have hu : ∀ j, u j = bm (e j) L - 1 := fun j => (heu j).symm
    simp only [hu]
    rw [sum_e (fun U => bm (e i) U * (bm U L - 1))]
    have h := hq.sq (e i) L
    have hne : e i ≠ L := ((hext (e i)).mp (hemem i)).1
    have h0 : t (e i) = 0 := (Finset.mem_filter.mp (hemem i)).2
    rw [if_neg hne, h0, sum_split, bLL, hq.symm R L, bLR] at h
    have hrow := hq.row (e i)
    rw [sum_split, h0] at hrow
    have h1 := hUR (e i) (hemem i)
    have e2 : ∑ U ∈ ext, bm (e i) U * (bm U L - 1) = ∑ U ∈ ext, bm (e i) U * bm U L -
        ∑ U ∈ ext, bm (e i) U := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun U _ => by ring)
    rw [e2]
    nlinarith
  · intro i j
    have hu : ∀ j, u j = bm (e j) L - 1 := fun j => (heu j).symm
    rw [hu i, hu j]
    rw [sum_e (fun U => bm (e i) U * bm U (e j))]
    have h := hq.sq (e i) (e j)
    have h0i : t (e i) = 0 := (Finset.mem_filter.mp (hemem i)).2
    have h0j : t (e j) = 0 := (Finset.mem_filter.mp (hemem j)).2
    rw [h0i, h0j, sum_split] at h
    have hij : (e i = e j) ↔ (i = j) := he.eq_iff
    have h1 := hUR (e i) (hemem i)
    have h2 := hUR (e j) (hemem j)
    rw [hq.symm L (e j), hq.symm R (e j)] at h
    have hLj : bm (e j) R = 2 - bm (e j) L := by linarith
    have hLi : bm (e i) R = 2 - bm (e i) L := by linarith
    rw [hLj, hLi] at h
    by_cases hij' : i = j
    · subst hij'; simp only [if_pos rfl] at h ⊢; nlinarith
    · rw [if_neg (fun h' => hij' (hij.mp h')), if_neg hij'] at *; nlinarith
  · intro hz i
    exact hz (e i)

end Conway7
