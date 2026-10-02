import Conway7.Assembly
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Fintype.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# From the graph to the relabelled adjacency matrix (paper, Sections 2–3)

* `sp`, `exists_relabel_free`: a fixed-point-free permutation with `σ^[7] = id` is, after
  relabelling, the shift `(U, b) ↦ (U, b + 1)` on `Fin m × ZMod 7`;
* `unique_fixed`: an automorphism `σ ≠ 1` of an `srg(99,14,1,2)` with `σ^[7] = id` has exactly one
  fixed vertex (paper, Lemma 3.1);
* `no_order7`: such an automorphism does not exist.
-/

open Finset Matrix

namespace Conway7

section relabel

variable {V : Type*} [Fintype V] [DecidableEq V] (σ : V ≃ V)

/-- `σ ^ k` for `k : ZMod 7`. -/
def sp (k : ZMod 7) (v : V) : V := σ^[k.val] v

variable {σ}

theorem iter_mod (h7 : ∀ v, σ^[7] v = v) (n : ℕ) (v : V) : σ^[n % 7] v = σ^[n] v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with hn | hn
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      rw [show (m + 7) % 7 = m % 7 by omega, ih m (by omega), Function.iterate_add_apply,
        h7 v]

theorem sp_add (h7 : ∀ v, σ^[7] v = v) (a b : ZMod 7) (v : V) :
    sp σ (a + b) v = sp σ a (sp σ b v) := by
  simp only [sp]
  rw [ZMod.val_add, iter_mod h7, Function.iterate_add_apply]

theorem sp_zero (v : V) : sp σ 0 v = v := by simp [sp]

theorem sp_one (v : V) : sp σ 1 v = σ v := rfl

theorem sp_eq_self (h7 : ∀ v, σ^[7] v = v) (hfree : ∀ v, σ v ≠ v) {k : ZMod 7} {v : V}
    (h : sp σ k v = v) : k = 0 := by
  by_contra hk
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hn : ∀ n : ℕ, sp σ (n * k) v = v := by
    intro n
    induction n with
    | zero => simp [sp_zero]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ZMod 7) * k = n * k + k by push_cast; ring, sp_add h7, h, ih]
  have h1 := hn (k⁻¹).val
  rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hk, sp_one] at h1
  exact hfree v h1

/-- The orbit relation of `σ`. -/
def orbitSetoid (h7 : ∀ v, σ^[7] v = v) : Setoid V where
  r v w := ∃ k : ZMod 7, w = sp σ k v
  iseqv := by
    refine ⟨fun v => ⟨0, (sp_zero v).symm⟩, ?_, ?_⟩
    · rintro v w ⟨k, rfl⟩
      exact ⟨-k, by rw [← sp_add h7, neg_add_cancel, sp_zero]⟩
    · rintro v w x ⟨k, rfl⟩ ⟨l, rfl⟩
      exact ⟨l + k, by rw [sp_add h7]⟩

theorem exists_relabel_free (h7 : ∀ v, σ^[7] v = v) (hfree : ∀ v, σ v ≠ v) :
    ∃ m : ℕ, ∃ e : Fin m × ZMod 7 ≃ V, ∀ U b, e (U, b + 1) = σ (e (U, b)) := by
  classical
  let S := orbitSetoid h7
  let O := Quotient S
  let φ : O × ZMod 7 → V := fun p => sp σ p.2 p.1.out
  have hinj : Function.Injective φ := by
    rintro ⟨o, b⟩ ⟨o', b'⟩ h
    simp only [φ] at h
    have hoo : o = o' := by
      rw [← Quotient.out_eq o, ← Quotient.out_eq o']
      apply Quotient.sound
      refine ⟨-b' + b, ?_⟩
      rw [sp_add h7, h, ← sp_add h7, neg_add_cancel, sp_zero]
    subst hoo
    have : sp σ (b - b') (sp σ b' o.out) = sp σ b' o.out := by
      rw [← sp_add h7, sub_add_cancel, h]
    have hk := sp_eq_self h7 hfree this
    simp only [Prod.mk.injEq, true_and]
    exact (sub_eq_zero.mp hk)
  have hsurj : Function.Surjective φ := by
    intro v
    obtain ⟨k, hk⟩ : S (Quotient.mk S v).out v := Quotient.mk_out (s := S) v
    exact ⟨(Quotient.mk S v, k), hk.symm⟩
  let E : O × ZMod 7 ≃ V := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  let F : Fin (Fintype.card O) ≃ O := (Fintype.equivFin O).symm
  refine ⟨Fintype.card O, (Equiv.prodCongr F (Equiv.refl _)).trans E, ?_⟩
  intro U b
  change sp σ (b + 1) (F U).out = σ (sp σ b (F U).out)
  rw [add_comm, sp_add h7, sp_one]

/-- `σ` preserves the set of its non-fixed points. -/
theorem not_fixed_iff (σ : V ≃ V) (v : V) : ¬ σ v = v ↔ ¬ σ (σ v) = σ v :=
  not_congr σ.injective.eq_iff.symm

/-- The restriction of `σ` to its non-fixed points. -/
def σfree (σ : V ≃ V) : {v // ¬ σ v = v} ≃ {v // ¬ σ v = v} :=
  Equiv.subtypeEquiv (p := fun v => ¬ σ v = v) (q := fun v => ¬ σ v = v) σ (not_fixed_iff σ)

theorem σfree_apply (σ : V ≃ V) (v : {v // ¬ σ v = v}) : (σfree σ v).1 = σ v.1 := rfl

theorem σfree_iter (σ : V ≃ V) (n : ℕ) (v : {v // ¬ σ v = v}) :
    ((σfree σ)^[n] v).1 = σ^[n] v.1 := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, σfree_apply, Function.iterate_succ_apply]

/-- The number of non-fixed points is divisible by 7. -/
theorem seven_dvd_card_nonfixed (σ : V ≃ V) (h7 : ∀ v, σ^[7] v = v) :
    7 ∣ Fintype.card {v // ¬ σ v = v} := by
  obtain ⟨m, e, -⟩ := exists_relabel_free (σ := σfree σ)
    (fun v => Subtype.ext (by rw [σfree_iter]; exact h7 v.1))
    (fun v h => v.2 (by have := congrArg Subtype.val h; simpa only [σfree_apply] using this))
  have h := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card] at h
  exact ⟨m, by rw [← h, mul_comm]⟩

end relabel

section graph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma iter_aut (σ : G ≃g G) (n : ℕ) (v : V) : (σ.toEquiv)^[n] v = (⇑σ)^[n] v := rfl

/-- A common neighbour of two non-adjacent fixed points is fixed (`μ = 2`, `7` is odd). -/
theorem common_nbr_fixed {n k ℓ : ℕ} (hG : G.IsSRGWith n k ℓ 2) (σ : G ≃g G)
    (h7 : ∀ v, (⇑σ)^[7] v = v) {u v : V} (hu : σ u = u) (hv : σ v = v) (huv : u ≠ v)
    (hnadj : ¬ G.Adj u v) {w : V} (huw : G.Adj u w) (hvw : G.Adj v w) : σ w = w := by
  have hmem : ∀ x, G.Adj u x → G.Adj v x → G.Adj u (σ x) ∧ G.Adj v (σ x) := by
    intro x hux hvx
    constructor
    · have h := σ.map_adj_iff (v := u) (w := x)
      rw [hu] at h
      exact h.mpr hux
    · have h := σ.map_adj_iff (v := v) (w := x)
      rw [hv] at h
      exact h.mpr hvx
  obtain ⟨h1u, h1v⟩ := hmem w huw hvw
  obtain ⟨h2u, h2v⟩ := hmem (σ w) h1u h1v
  by_contra hw
  have hd2 : σ (σ w) ≠ σ w := fun h => hw (σ.injective h)
  -- the two common neighbours are `w` and `σ w`, so `σ (σ w) = w`
  have hcard := hG.of_not_adj huv hnadj
  have hσσ : σ (σ w) = w := by
    by_contra h3
    have h3lt : 2 < Fintype.card (G.commonNeighbors u v) := by
      rw [Fintype.two_lt_card_iff]
      refine ⟨⟨w, (G.mem_commonNeighbors).mpr ⟨huw, hvw⟩⟩,
        ⟨σ w, (G.mem_commonNeighbors).mpr ⟨h1u, h1v⟩⟩,
        ⟨σ (σ w), (G.mem_commonNeighbors).mpr ⟨h2u, h2v⟩⟩, ?_, ?_, ?_⟩
      · intro h; exact hw (congrArg Subtype.val h).symm
      · intro h; exact h3 (congrArg Subtype.val h).symm
      · intro h; exact hd2 (congrArg Subtype.val h).symm
    omega
  -- then `σ^7 w = σ w`
  have h2 : ∀ m : ℕ, (⇑σ)^[2 * m] w = w := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, Function.iterate_add_apply]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hσσ, ih]
  have := h7 w
  rw [show 7 = 1 + 2 * 3 by rfl, Function.iterate_add_apply, h2 3] at this
  exact hw this

/-- A vertex adjacent to two distinct fixed vertices is fixed. -/
theorem fixed_of_two_fixed (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h7 : ∀ v, (⇑σ)^[7] v = v) {a b v : V} (ha : σ a = a) (hb : σ b = b) (hab : a ≠ b)
    (hav : G.Adj a v) (hbv : G.Adj b v) : σ v = v := by
  by_cases hadj : G.Adj a b
  · have hcard := hG.of_adj a b hadj
    have hσa : G.Adj a (σ v) := by
      have h := σ.map_adj_iff (v := a) (w := v)
      rw [ha] at h
      exact h.mpr hav
    have hσb : G.Adj b (σ v) := by
      have h := σ.map_adj_iff (v := b) (w := v)
      rw [hb] at h
      exact h.mpr hbv
    have h1 := Fintype.card_le_one_iff.mp (le_of_eq hcard)
      ⟨σ v, (G.mem_commonNeighbors).mpr ⟨hσa, hσb⟩⟩ ⟨v, (G.mem_commonNeighbors).mpr ⟨hav, hbv⟩⟩
    exact congrArg Subtype.val h1
  · exact common_nbr_fixed hG σ h7 ha hb hab hadj hav hbv

/-- The number of fixed neighbours of `y`. -/
def nfix (σ : G ≃g G) (y : V) : ℕ := (univ.filter (fun v => G.Adj y v ∧ σ v = v)).card

/-- The number of non-fixed neighbours of `y`. -/
def nnon (σ : G ≃g G) (y : V) : ℕ := (univ.filter (fun v => G.Adj y v ∧ ¬ σ v = v)).card

theorem nfix_add_nnon (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (x : V) :
    nfix σ x + nnon σ x = 14 := by
  have h := Finset.card_filter_add_card_filter_not (s := G.neighborFinset x) (fun v => σ v = v)
  rw [SimpleGraph.card_neighborFinset_eq_degree, hG.regular x, SimpleGraph.neighborFinset_eq_filter,
    Finset.filter_filter, Finset.filter_filter] at h
  exact h

/-- The non-fixed neighbours of a fixed vertex form orbits of size 7. -/
theorem nnon_mod7 (σ : G ≃g G) (h7 : ∀ v, (⇑σ)^[7] v = v) {x : V} (hx : σ x = x) :
    7 ∣ nnon σ x := by
  have hmem : ∀ v, G.Adj x v ↔ G.Adj x (σ v) := by
    intro v
    have h := σ.map_adj_iff (v := x) (w := v)
    rw [hx] at h
    exact h.symm
  let τ : {v // G.Adj x v} ≃ {v // G.Adj x v} :=
    Equiv.subtypeEquiv (p := fun v => G.Adj x v) (q := fun v => G.Adj x v) σ.toEquiv hmem
  have hτi : ∀ (n : ℕ) (w : {v // G.Adj x v}), (τ^[n] w).1 = (⇑σ)^[n] w.1 := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih => intro w; rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]; rfl
  have hτ : ∀ w, τ^[7] w = w := fun w => Subtype.ext (by rw [hτi]; exact h7 w.1)
  have hdvd := seven_dvd_card_nonfixed τ hτ
  have hcard : Fintype.card {w : {v // G.Adj x v} // ¬ τ w = w} = nnon σ x := by
    unfold nnon
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr ((Equiv.subtypeEquivRight fun w => ?_).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun v => G.Adj x v) (fun v => ¬ σ v = v)))
    simp [τ, Subtype.ext_iff]
  rwa [hcard] at hdvd

/-- `nfix x` is even: `λ = 1` pairs the fixed neighbours of `x`. -/
theorem nfix_even (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h7 : ∀ v, (⇑σ)^[7] v = v)
    {x : V} (hx : σ x = x) : Even (nfix σ x) := by
  have hex : ∀ u : {v // G.Adj x v ∧ σ v = v}, ∃ w : {v // G.Adj x v ∧ σ v = v},
      G.Adj u.1 w.1 := by
    intro u
    have hc := hG.of_adj x u.1 u.2.1
    obtain ⟨c⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (G.commonNeighbors x u.1))
    have hcm := (G.mem_commonNeighbors).mp c.2
    have hfc : σ c = c := fixed_of_two_fixed hG σ h7 hx u.2.2 (G.ne_of_adj u.2.1) hcm.1 hcm.2
    exact ⟨⟨c.1, hcm.1, hfc⟩, hcm.2⟩
  have huniq : ∀ u w w' : {v // G.Adj x v ∧ σ v = v}, G.Adj u.1 w.1 → G.Adj u.1 w'.1 → w = w' := by
    intro u w w' hw hw'
    have hc := hG.of_adj x u.1 u.2.1
    have h1 := Fintype.card_le_one_iff.mp (le_of_eq hc)
      ⟨w.1, (G.mem_commonNeighbors).mpr ⟨w.2.1, hw⟩⟩ ⟨w'.1, (G.mem_commonNeighbors).mpr ⟨w'.2.1, hw'⟩⟩
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  choose f hf using hex
  have hinv : Function.Involutive f := fun u => huniq (f u) (f (f u)) u (hf (f u)) (hf u).symm
  have hfree : ∀ u, f u ≠ u := by
    intro u h
    have h' := hf u
    rw [h] at h'
    exact G.ne_of_adj h' rfl
  have hπ2 : (hinv.toPerm f) ^ 2 = 1 := by
    ext u
    simp [sq, hinv u]
  have hsupp : (hinv.toPerm f).support = univ := by
    apply Finset.eq_univ_of_forall
    intro u
    rw [Equiv.Perm.mem_support]
    exact hfree u
  have h2 := Equiv.Perm.two_dvd_card_support hπ2
  rw [hsupp, Finset.card_univ, Fintype.card_subtype] at h2
  exact even_iff_two_dvd.mpr h2

/-- If a fixed vertex has all its 14 neighbours fixed, every vertex is fixed. -/
theorem all_fixed_of_nfix14 (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G)
    (h7 : ∀ v, (⇑σ)^[7] v = v) {x : V} (hx : σ x = x) (h14 : nfix σ x = 14) : ∀ v, σ v = v := by
  have hn := nfix_add_nnon hG σ x
  have h0 : nnon σ x = 0 := by omega
  have hnb : ∀ v, G.Adj x v → σ v = v := by
    intro v hv
    by_contra hne
    have hmem : v ∈ univ.filter (fun v => G.Adj x v ∧ ¬ σ v = v) := by simp [hv, hne]
    unfold nnon at h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hmem
    exact Finset.notMem_empty v hmem
  intro v
  by_cases hvx : v = x
  · rw [hvx]
    exact hx
  by_cases hadj : G.Adj x v
  · exact hnb v hadj
  have hcard := hG.of_not_adj (fun h => hvx h.symm) hadj
  obtain ⟨a, b, hab⟩ :=
    Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card (G.commonNeighbors x v))
  have ha := (G.mem_commonNeighbors).mp a.2
  have hb := (G.mem_commonNeighbors).mp b.2
  exact fixed_of_two_fixed hG σ h7 (hnb _ ha.1) (hnb _ hb.1) (fun h => hab (Subtype.ext h))
    ha.2.symm hb.2.symm

/-- **Paper, Lemma 3.1.** An automorphism `σ ≠ 1` with `σ^[7] = id` of an `srg(99,14,1,2)` fixes
exactly one vertex. -/
theorem unique_fixed (hG : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (h7 : ∀ v, (⇑σ)^[7] v = v)
    (hne : ∃ v, σ v ≠ v) : ∃ x, σ x = x ∧ ∀ y, σ y = y → y = x := by
  -- existence: the non-fixed points come in orbits of size 7, and `7 ∤ 99`
  have hdvd := seven_dvd_card_nonfixed σ.toEquiv h7
  have hsum : Fintype.card {v // σ v = v} + Fintype.card {v // ¬ σ v = v} = 99 := by
    rw [Fintype.card_subtype_compl, hG.card]
    have : Fintype.card {v // σ v = v} ≤ 99 := by
      rw [← hG.card]; exact Fintype.card_subtype_le _
    omega
  have hcardF : Fintype.card {v // σ.toEquiv v = v} = Fintype.card {v // σ v = v} := rfl
  have hpos : 0 < Fintype.card {v // σ v = v} := by
    have : Fintype.card {v // ¬ σ.toEquiv v = v} = Fintype.card {v // ¬ σ v = v} := rfl
    rw [this] at hdvd
    omega
  obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp hpos
  refine ⟨x, hx, ?_⟩
  -- every fixed vertex has no fixed neighbour
  have hnf : ∀ z, σ z = z → nfix σ z = 0 := by
    intro z hz
    have h1 := nfix_add_nnon hG σ z
    have h2 := nnon_mod7 σ h7 hz
    have h3 := nfix_even hG σ h7 hz
    obtain ⟨v, hv⟩ := hne
    have h14 : nfix σ z ≠ 14 := fun h => hv (all_fixed_of_nfix14 hG σ h7 hz h v)
    obtain ⟨r, hr⟩ := h3
    omega
  intro y hy
  by_contra hyx
  have h0 := hnf x hx
  by_cases hadj : G.Adj x y
  · have hmem : y ∈ univ.filter (fun v => G.Adj x v ∧ σ v = v) := by simp [hadj, hy]
    unfold nfix at h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hmem
    exact Finset.notMem_empty y hmem
  · have hcard := hG.of_not_adj (fun h => hyx h.symm) hadj
    obtain ⟨c⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card (G.commonNeighbors x y))
    have hcm := (G.mem_commonNeighbors).mp c.2
    have hc : σ c = c := common_nbr_fixed hG σ h7 hx hy (fun h => hyx h.symm) hadj hcm.1 hcm.2
    have hmem : c.1 ∈ univ.filter (fun v => G.Adj x v ∧ σ v = v) := by simp [hcm.1, hc]
    unfold nfix at h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hmem
    exact Finset.notMem_empty _ hmem

end graph

end Conway7
