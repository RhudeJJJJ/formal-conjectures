/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-! Exact finite critical-independent-set definitions and elementary exchange lemmas.
Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization. -/
namespace CriticalIndependentProof
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def neighborhood (G : SimpleGraph V) (I : Finset V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ u ∈ I, G.Adj u v

omit [DecidableEq V] in
@[simp] lemma mem_neighborhood (G : SimpleGraph V) (I : Finset V) (v : V) :
    v ∈ neighborhood G I ↔ ∃ u ∈ I, G.Adj u v := by
  classical
  simp [neighborhood]

omit [DecidableEq V] in
@[simp] lemma neighborhood_empty (G : SimpleGraph V) : neighborhood G ∅ = ∅ := by
  ext v; simp

noncomputable def difference (G : SimpleGraph V) (I : Finset V) : ℤ :=
  (I.card : ℤ) - (neighborhood G I).card

def IsCritical (G : SimpleGraph V) (I : Finset V) : Prop :=
  G.IsIndepSet (I : Set V) ∧ ∀ J : Finset V,
    G.IsIndepSet (J : Set V) → difference G J ≤ difference G I

def IsMaximumCritical (G : SimpleGraph V) (I : Finset V) : Prop :=
  IsCritical G I ∧ ∀ J : Finset V, IsCritical G J → J.card ≤ I.card

noncomputable def criticalUnion (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, IsMaximumCritical G I ∧ v ∈ I

@[simp] lemma mem_criticalUnion (G : SimpleGraph V) (v : V) :
    v ∈ criticalUnion G ↔ ∃ I : Finset V, IsMaximumCritical G I ∧ v ∈ I := by
  classical
  simp [criticalUnion]

lemma maximumCritical_exists (G : SimpleGraph V) : ∃ I, IsMaximumCritical G I := by
  classical
  let inds := univ.powerset.filter fun I : Finset V => G.IsIndepSet (I : Set V)
  have he : (∅ : Finset V) ∈ inds := by simp [inds]
  obtain ⟨I, hI, hmax⟩ := inds.exists_max_image (difference G) ⟨∅, he⟩
  have hIc : IsCritical G I := ⟨(mem_filter.mp hI).2, fun J hJ =>
    hmax J (by simp [inds, hJ])⟩
  let crits := univ.powerset.filter (IsCritical G)
  obtain ⟨K, hK, hkm⟩ := crits.exists_max_image card ⟨I, by simp [crits, hIc]⟩
  exact ⟨K, (mem_filter.mp hK).2, fun J hJ => hkm J (by simp [crits, hJ])⟩

omit [DecidableEq V] in
lemma critical_nonnegative (G : SimpleGraph V) {I : Finset V} (hI : IsCritical G I) :
    0 ≤ difference G I := by
  have := hI.2 ∅ (by simp)
  simpa [difference] using this

omit [DecidableEq V] in
lemma critical_of_improvement (G : SimpleGraph V) {I J : Finset V}
    (hI : IsCritical G I) (hJ : G.IsIndepSet (J : Set V))
    (h : difference G I ≤ difference G J) : IsCritical G J :=
  ⟨hJ, fun K hK => (hI.2 K hK).trans h⟩

omit [Fintype V] [DecidableEq V] in
lemma independent_no_edge (G : SimpleGraph V) {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) {u v : V} (hu : u ∈ I) (hv : v ∈ I) :
    ¬G.Adj u v := by
  by_cases h : u = v
  · subst v; exact G.irrefl
  · exact hI hu hv h

omit [Fintype V] in
lemma independent_insert (G : SimpleGraph V) {I : Finset V} {p : V}
    (hI : G.IsIndepSet (I : Set V)) (hp : ∀ u ∈ I, ¬G.Adj p u) :
    G.IsIndepSet ((insert p I : Finset V) : Set V) := by
  intro u hu v hv huv
  simp only [coe_insert, Set.mem_insert_iff] at hu hv
  rcases hu with rfl | hu <;> rcases hv with rfl | hv
  · exact (huv rfl).elim
  · exact hp v hv
  · exact fun h => hp u hu h.symm
  · exact hI hu hv huv

/-- A leaf belongs to the union, not necessarily to every maximum critical set. -/
theorem leaf_mem_union (G : SimpleGraph V) {p s : V}
    (hps : G.Adj p s) (hp : ∀ v, G.Adj p v → v = s) : p ∈ criticalUnion G := by
  classical
  obtain ⟨I, hI⟩ := maximumCritical_exists G
  by_cases hpI : p ∈ I
  · exact (mem_criticalUnion G _).mpr ⟨I, hI, hpI⟩
  by_cases hsI : s ∈ I
  · let J := insert p (I.erase s)
    have hJ : G.IsIndepSet (J : Set V) := independent_insert G
      (hI.1.1.mono (by intro v hv; exact (mem_erase.mp hv).2)) (by
        intro v hv he
        exact (mem_erase.mp hv).1 (hp v he))
    have hpNI : p ∈ neighborhood G I := (mem_neighborhood G _ _).mpr ⟨s, hsI, hps.symm⟩
    have hsNI : s ∉ neighborhood G I := by
      intro h
      obtain ⟨u, hu, he⟩ := (mem_neighborhood G _ _).mp h
      exact independent_no_edge G hI.1.1 hu hsI he
    have hsub : neighborhood G J ⊆ insert s ((neighborhood G I).erase p) := by
      intro v hv
      obtain ⟨u, hu, he⟩ := (mem_neighborhood G _ _).mp hv
      rcases mem_insert.mp hu with rfl | hu
      · exact mem_insert_self _ _ |> fun h => (hp v he) ▸ h
      · have huI := (mem_erase.mp hu).2
        have hvp : v ≠ p := by
          intro h; subst v
          exact (mem_erase.mp hu).1 (hp u he.symm)
        exact mem_insert_of_mem (mem_erase.mpr ⟨hvp,
          (mem_neighborhood G _ _).mpr ⟨u, huI, he⟩⟩)
    have hcard : J.card = I.card := by
      simp [J, hpI, hsI, card_erase_of_mem]
      have := card_pos.mpr ⟨s, hsI⟩
      omega
    have hnc : (neighborhood G J).card ≤ (neighborhood G I).card := by
      have := card_le_card hsub
      have hsE : s ∉ (neighborhood G I).erase p := fun h => hsNI (mem_of_mem_erase h)
      rw [card_insert_of_notMem hsE, card_erase_of_mem hpNI] at this
      have := card_pos.mpr ⟨p, hpNI⟩
      omega
    have hJc : IsCritical G J := critical_of_improvement G hI.1 hJ (by
      unfold difference; rw [hcard]; exact sub_le_sub_left (Int.ofNat_le.mpr hnc) _)
    exact (mem_criticalUnion G _).mpr ⟨J, ⟨hJc, fun K hK => hcard ▸ hI.2 K hK⟩,
      mem_insert_self _ _⟩
  · have hJ : G.IsIndepSet ((insert p I : Finset V) : Set V) := independent_insert G hI.1.1
      (by intro v hv he; exact hsI ((hp v he) ▸ hv))
    have hsub : neighborhood G (insert p I) ⊆ insert s (neighborhood G I) := by
      intro v hv
      obtain ⟨u, hu, he⟩ := (mem_neighborhood G _ _).mp hv
      rcases mem_insert.mp hu with rfl | hu
      · exact (hp v he) ▸ mem_insert_self _ _
      · exact mem_insert_of_mem ((mem_neighborhood G _ _).mpr ⟨u, hu, he⟩)
    have hnc : (neighborhood G (insert p I)).card ≤ (neighborhood G I).card + 1 :=
      (card_le_card hsub).trans (card_insert_le _ _)
    have hJc := critical_of_improvement G hI.1 hJ (by
      unfold difference
      rw [card_insert_of_notMem hpI]
      omega)
    have := hI.2 (insert p I) hJc
    rw [card_insert_of_notMem hpI] at this
    omega
end CriticalIndependentProof
