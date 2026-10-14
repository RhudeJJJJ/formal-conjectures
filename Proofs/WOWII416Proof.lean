/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.CriticalIndependentProof

/-! WOWII416, strengthened without the subtractive constant. Written source:
Jonas J. Gebendorfer, A Universal-Vertex Reduction for Critical Independent Sets
and WOWII Conjecture416, 31 August2026. The proof below formalizes the strengthened
inequality, not every auxiliary equality in the manuscript. -/
namespace WOWII416Proof
open SimpleGraph Finset CriticalIndependentProof
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def leaves (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => G.degree v = 1

noncomputable def doubleNeighborhood (G : SimpleGraph V) : Finset V :=
  neighborhood G (neighborhood G (leaves G))

noncomputable def isolatesOn (G : SimpleGraph V) (Q : Finset V) : Finset V := by
  classical
  exact Q.filter fun v => ∀ w ∈ Q, ¬G.Adj v w

omit [Fintype V] [DecidableEq V] in
lemma support_universal (G : SimpleGraph V) (hc : G.Connected)
    (hd : ∀ u v, G.dist u v ≤ 2) {p s : V}
    (hps : G.Adj p s) (hp : ∀ v, G.Adj p v → v = s) :
    ∀ v, v ≠ s → G.Adj s v := by
  intro v hvs
  obtain ⟨w, hw⟩ := hc.exists_walk_length_eq_dist p v
  have hl : w.length ≤ 2 := hw ▸ hd p v
  cases w with
  | nil => exact hps.symm
  | @cons _ a _ hpa tail =>
    have ha : a = s := hp a hpa
    subst a
    cases tail with
    | nil => exact (hvs rfl).elim
    | @cons _ b _ hsb rest =>
      cases rest with
      | nil => exact hsb
      | cons _ _ => simp only [Walk.length_cons] at hl; omega

lemma leaf_mem (G : SimpleGraph V) {p : V} (hp : p ∈ leaves G) :
    p ∈ criticalUnion G := by
  classical
  have hdeg : G.degree p = 1 := (mem_filter.mp hp).2
  obtain ⟨s, hps, hs⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hdeg
  exact leaf_mem_union G hps hs

lemma isolates_subset_leaves (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V) (hd : ∀ u v, G.dist u v ≤ 2) :
    isolatesOn G (doubleNeighborhood G) ⊆ leaves G := by
  classical
  intro v hv
  obtain ⟨hvQ, hvi⟩ := mem_filter.mp hv
  obtain ⟨s, hs, hsv⟩ := (mem_neighborhood G _ _).mp hvQ
  obtain ⟨p, hp, hps⟩ := (mem_neighborhood G _ _).mp hs
  have hpd : G.degree p = 1 := (mem_filter.mp hp).2
  obtain ⟨t, hpt, hpu⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hpd
  have ht : t = s := (hpu _ hps).symm
  subst t
  have hu := support_universal G hc hd hps hpu
  have hsnotleaf : s ∉ leaves G := by
    intro h
    have hsd : G.degree s = 1 := (mem_filter.mp h).2
    have hneigh : G.neighborFinset s = univ.erase s := by
      ext w
      simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
      exact ⟨fun h => h.ne.symm, hu w⟩
    have hcdeg : G.degree s = Fintype.card V - 1 := by
      rw [← G.card_neighborFinset_eq_degree, hneigh, card_erase_of_mem (mem_univ s), card_univ]
    omega
  have hQ : doubleNeighborhood G = univ.erase s := by
    ext w
    simp only [doubleNeighborhood, mem_neighborhood, mem_erase, mem_univ, and_true]
    constructor
    · rintro ⟨z, ⟨q, hq, hqz⟩, hzw⟩
      have hqs : q ≠ s := fun he => hsnotleaf (he ▸ hq)
      have hqd : G.degree q = 1 := (mem_filter.mp hq).2
      obtain ⟨z', hqz', hqu⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hqd
      have hzs : z = s := (hqu _ hqz).trans ((hqu _ (hu q hqs).symm).symm)
      subst z
      exact hzw.ne.symm
    · intro hws
      exact ⟨s, ⟨p, hp, hps⟩, hu w hws⟩
  have hvs : v ≠ s := by simpa [hQ] using hvQ
  have huniq : ∀ w, G.Adj v w → w = s := by
    intro w hvw
    by_contra hws
    exact hvi w (by simp [hQ, hws]) hvw
  have hdv : G.degree v = 1 := G.degree_eq_one_iff_existsUnique_adj.mpr
    ⟨s, (hu v hvs).symm, huniq⟩
  exact mem_filter.mpr ⟨mem_univ _, hdv⟩

/-- Stronger than the printed inequality by two, for every finite graph in its domain. -/
theorem strengthened416 (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V) (hd : ∀ u v, G.dist u v ≤ 2) :
    (isolatesOn G (doubleNeighborhood G)).card ≤ (criticalUnion G).card := by
  classical
  apply card_le_card
  intro v hv
  exact leaf_mem G (isolates_subset_leaves G hc hn hd hv)

/-- Integer subtraction preserves the printed minus-two bound, including zero isolates. -/
theorem conjecture416 (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V) (hd : ∀ u v, G.dist u v ≤ 2) :
    ((isolatesOn G (doubleNeighborhood G)).card : ℤ) - 2 ≤ (criticalUnion G).card := by
  have := strengthened416 G hc hn hd
  omega
end WOWII416Proof
