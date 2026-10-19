import Proofs.TDANeighborhood

/-! A generic cover with forced vertices and explicit degree-one core correction. -/

namespace TotalDominationAnnihilationProof
open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- A symmetric neighborhood system can be covered after the forced vertices
and the neighbors of its degree-one vertices have been selected. -/
theorem core_cover (K S : Finset V) (N : V → Finset V)
    (hNS : ∀ v ∈ K, N v ⊆ K) (hsym : ∀ u v, v ∈ N u ↔ u ∈ N v)
    (hnon : ∀ v ∈ K, (N v).Nonempty) (hSK : S ⊆ K)
    (hone : ∀ v ∈ K, (N v).card = 1 → v ∈ S) :
    ∃ D : Finset V, D ⊆ K ∧ S ⊆ D ∧ (∀ v ∈ K, ∃ w ∈ D, w ∈ N v) ∧
      6 * D.card ≤ 3 * K.card + 4 * S.card +
        2 * (K.filter (fun v => (N v).card = 1)).card +
        (K.filter (fun v => (N v).card = 2)).card := by
  let R := K.filter (fun v => (N v).card = 1)
  have hRS : R ⊆ S := by
    intro v hv
    exact hone v (mem_filter.mp hv).1 (mem_filter.mp hv).2
  have hex : ∀ v : R, ∃ w, N v.val = {w} := by
    intro v
    exact card_eq_one.mp (mem_filter.mp v.property).2
  choose f hf using hex
  let T := (R.attach.image f) \ S
  let D0 := S ∪ T
  let B := K.filter fun v => ∃ w ∈ D0, w ∈ N v
  let Q := K \ D0
  let J := K \ B
  have hTK : T ⊆ K := by
    intro w hw
    obtain ⟨hwim, _⟩ := mem_sdiff.mp hw
    obtain ⟨v, _, rfl⟩ := mem_image.mp hwim
    exact hNS v.val (mem_filter.mp v.property).1 (by rw [hf v]; simp)
  have hD0K : D0 ⊆ K := union_subset hSK hTK
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    intro v hvS hvT
    exact (mem_sdiff.mp hvT).2 hvS
  have hTc : T.card ≤ R.card := by
    calc
      _ ≤ (R.attach.image f).card := card_le_card sdiff_subset
      _ ≤ R.attach.card := card_image_le
      _ = _ := card_attach
  have hRB : R ⊆ B := by
    intro v hv
    let vv : R := ⟨v, hv⟩
    have hfD : f vv ∈ D0 := by
      by_cases hs : f vv ∈ S
      · exact mem_union_left _ hs
      · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_image.mpr ⟨vv, mem_attach _ _, rfl⟩, hs⟩)
    exact mem_filter.mpr ⟨(mem_filter.mp hv).1, f vv, hfD, by rw [hf vv]; simp⟩
  have hTB : T ⊆ B := by
    intro w hw
    obtain ⟨v, _, hfw⟩ := mem_image.mp (mem_sdiff.mp hw).1
    have hvS : v.val ∈ S := hRS v.property
    have hwN : w ∈ N v.val := by rw [← hfw, hf v]; simp
    exact mem_filter.mpr ⟨hTK hw, v.val, mem_union_left _ hvS, (hsym _ _).mp hwN⟩
  have hRTdis : Disjoint R T := disjoint_of_subset_left hRS hdis
  have hBcard : R.card + T.card ≤ B.card := by
    rw [← card_union_of_disjoint hRTdis]
    exact card_le_card (union_subset hRB hTB)
  have hJsub : ∀ v ∈ J, N v ⊆ Q := by
    intro v hv w hwN
    obtain ⟨hvK, hvB⟩ := mem_sdiff.mp hv
    refine mem_sdiff.mpr ⟨hNS v hvK hwN, ?_⟩
    intro hwD
    exact hvB (mem_filter.mpr ⟨hvK, w, hwD, hwN⟩)
  have hJsize : ∀ v ∈ J, 2 ≤ (N v).card := by
    intro v hv
    have hvK := (mem_sdiff.mp hv).1
    have hp := card_pos.mpr (hnon v hvK)
    have hne : (N v).card ≠ 1 := by
      intro h1
      exact (mem_sdiff.mp hv).2 (hRB (mem_filter.mpr ⟨hvK, h1⟩))
    omega
  obtain ⟨X, hXQ, hXhit, hXb⟩ := Hypergraph.neighborhood_cover Q J N hJsub hJsize
  have htwo : (J.filter (fun v => (N v).card = 2)).card ≤
      (K.filter (fun v => (N v).card = 2)).card := by
    exact card_le_card (filter_subset_filter _ sdiff_subset)
  have hD0card : D0.card = S.card + T.card := card_union_of_disjoint hdis
  have hQcard : Q.card + D0.card = K.card := card_sdiff_add_card_eq_card hD0K
  have hBsub : B ⊆ K := filter_subset _ _
  have hJcard : J.card + B.card = K.card := card_sdiff_add_card_eq_card hBsub
  refine ⟨D0 ∪ X, union_subset hD0K (subset_trans hXQ sdiff_subset),
    subset_trans subset_union_left subset_union_left, ?_, ?_⟩
  · intro v hvK
    by_cases hvB : v ∈ B
    · obtain ⟨w, hwD, hwN⟩ := (mem_filter.mp hvB).2
      exact ⟨w, mem_union_left _ hwD, hwN⟩
    · obtain ⟨w, hwX, hwN⟩ := hXhit v (mem_sdiff.mpr ⟨hvK, hvB⟩)
      exact ⟨w, mem_union_right _ hwX, hwN⟩
  · have hc : (D0 ∪ X).card ≤ D0.card + X.card := card_union_le _ _
    change 6 * (D0 ∪ X).card ≤ 3 * K.card + 4 * S.card +
      2 * R.card + (K.filter (fun v => (N v).card = 2)).card
    omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.core_cover
