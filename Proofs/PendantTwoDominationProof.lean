import FormalConjectures.WrittenOnTheWallII.GraphConjecture393

/-! Complete proofs of the two explicit intersection variants 393b and 393c.
The constructions follow Gebendorfer, Simultaneous sharpness of three
pendant-neighborhood bounds for 2-domination, Propositions 3.4 and 3.5.
The source's missing set-operation glyph is not reconstructed.
OpenAI Codex assisted with formalization. -/

namespace PendantTwoDominationProof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture393

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

theorem completion_c :
    twoDominationNumber G ≤ (remainder G).card + (supports G).card +
      uniqueNeighborCount G (pendants G ∪ supports G) := by
  classical
  let L := univ.filter fun v => (G.neighborFinset v ∩ (pendants G ∪ supports G)).card = 1
  let D := remainder G ∪ supports G ∪ L
  have hD : IsTwoDominating G D := by
    intro v hv
    have hvU : v ∉ remainder G := fun h => hv (mem_union_left _ (mem_union_left _ h))
    have hvS : v ∉ supports G := fun h => hv (mem_union_left _ (mem_union_right _ h))
    have hvL : v ∉ L := fun h => hv (mem_union_right _ h)
    have hsome : ∃ s ∈ supports G, G.Adj s v := by
      simpa [remainder, neighbors] using hvU
    have hnoP : ∀ p ∈ pendants G, ¬ G.Adj v p := by
      intro p hp ha
      apply hvS
      simpa [supports, neighbors] using (show ∃ p ∈ pendants G, G.Adj p v from ⟨p, hp, ha.symm⟩)
    have heq : G.neighborFinset v ∩ (pendants G ∪ supports G) =
        G.neighborFinset v ∩ supports G := by
      ext w
      simp only [mem_inter, mem_union, mem_neighborFinset]
      constructor
      · rintro ⟨ha, hp | hs⟩
        · exact (hnoP w hp ha).elim
        · exact ⟨ha, hs⟩
      · exact fun h => ⟨h.1, Or.inr h.2⟩
    have hpos : 0 < (G.neighborFinset v ∩ supports G).card := by
      obtain ⟨s, hs, ha⟩ := hsome
      exact card_pos.mpr ⟨s, mem_inter.mpr ⟨by simpa using ha.symm, hs⟩⟩
    have hne : (G.neighborFinset v ∩ supports G).card ≠ 1 := by
      intro h
      exact hvL (by simp [L, heq, h])
    have hsub : G.neighborFinset v ∩ supports G ⊆ G.neighborFinset v ∩ D := by
      intro w hw
      exact mem_inter.mpr ⟨(mem_inter.mp hw).1,
        mem_union_left _ (mem_union_right _ (mem_inter.mp hw).2)⟩
    have := card_le_card hsub
    omega
  have hmin : twoDominationNumber G ≤ D.card :=
    csInf_le (OrderBot.bddBelow _) ⟨D, hD, rfl⟩
  have hcard : D.card ≤ (remainder G).card + (supports G).card + L.card :=
    (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  exact hmin.trans hcard

theorem conjecture393c_intersection (_hG : G.Connected) (_horder : 2 < Fintype.card V) :
    twoDominationNumber G ≤ (remainder G).card + (supports G).card +
      uniqueNeighborCount G (pendants G ∪ supports G) :=
  completion_c G

/-- The induced vertices of degree at least two are no more numerous than
the induced edges, by the degree-sum formula. -/
theorem card_high_degree_le_edges (A : Finset V) :
    (A.filter fun v => 2 ≤ (G.neighborFinset v ∩ A).card).card ≤ edgesOn G A := by
  classical
  let H := G.induce (A : Set V)
  have hdeg (v : (A : Set V)) :
      H.degree v = (G.neighborFinset v ∩ A).card := by
    have h := congrArg Finset.card (G.map_neighborFinset_induce v)
    simpa [H, card_neighborFinset_eq_degree] using h
  have hcard :
      (A.filter fun v => 2 ≤ (G.neighborFinset v ∩ A).card).card =
        (univ.filter fun v : (A : Set V) => 2 ≤ H.degree v).card := by
    rw [← card_map (f := Function.Embedding.subtype (· ∈ (A : Set V)))]
    congr 1
    ext v
    simp [hdeg]
  have he : H.edgeFinset.card = edgesOn G A :=
    (G.card_filter_edgeFinset_toFinset_subset A).symm
  let B := univ.filter fun v : (A : Set V) => 2 ≤ H.degree v
  have hsum : 2 * B.card ≤ ∑ v : (A : Set V), H.degree v := by
    calc
      2 * B.card = ∑ _v ∈ B, 2 := by simp [mul_comm]
      _ ≤ ∑ v ∈ B, H.degree v := sum_le_sum (fun v hv => (mem_filter.mp hv).2)
      _ ≤ ∑ v : (A : Set V), H.degree v := sum_le_sum_of_subset_of_nonneg
        (subset_univ _) (by intros; omega)
  rw [H.sum_degrees_eq_twice_card_edges, he] at hsum
  rw [hcard]
  dsimp [B] at hsum
  omega

/-- Completion from any subset, including the empty subset and isolated vertices. -/
theorem completion_b (A : Finset V) :
    twoDominationNumber G ≤ (univ \ neighbors G A).card + edgesOn G A +
      uniqueNeighborCount G A := by
  classical
  let U := univ \ neighbors G A
  let L := univ.filter fun v => (G.neighborFinset v ∩ A).card = 1
  let B := A.filter fun v => 2 ≤ (G.neighborFinset v ∩ A).card
  let D := U ∪ L ∪ B
  have hAD : A ⊆ D := by
    intro a ha
    by_cases hz : (G.neighborFinset a ∩ A).card = 0
    · apply mem_union_left
      apply mem_union_left
      simp only [U, mem_sdiff, mem_univ, true_and, neighbors, mem_filter,
        mem_univ, true_and, not_exists, not_and]
      intro w hw hwa
      have hm : w ∈ G.neighborFinset a ∩ A := mem_inter.mpr ⟨by simpa using hwa.symm, hw⟩
      have := card_pos.mpr ⟨w, hm⟩
      omega
    · by_cases ho : (G.neighborFinset a ∩ A).card = 1
      · exact mem_union_left _ (mem_union_right _ (by simp [L, ho]))
      · exact mem_union_right _ (by simp only [B, mem_filter]; exact ⟨ha, by omega⟩)
  have hD : IsTwoDominating G D := by
    intro v hv
    have hvU : v ∉ U := fun h => hv (mem_union_left _ (mem_union_left _ h))
    have hvL : v ∉ L := fun h => hv (mem_union_left _ (mem_union_right _ h))
    have hs : ∃ a ∈ A, G.Adj a v := by simpa [U, neighbors] using hvU
    have hp : 0 < (G.neighborFinset v ∩ A).card := by
      obtain ⟨a, ha, hav⟩ := hs
      exact card_pos.mpr ⟨a, mem_inter.mpr ⟨by simpa using hav.symm, ha⟩⟩
    have hn : (G.neighborFinset v ∩ A).card ≠ 1 := by
      intro h
      exact hvL (by simp [L, h])
    have hc := card_le_card (inter_subset_inter_left (G.neighborFinset v) hAD)
    omega
  have hmin : twoDominationNumber G ≤ D.card :=
    csInf_le (OrderBot.bddBelow _) ⟨D, hD, rfl⟩
  have hcard : D.card ≤ U.card + L.card + B.card :=
    (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hB := card_high_degree_le_edges G A
  change B.card ≤ edgesOn G A at hB
  change twoDominationNumber G ≤ U.card + edgesOn G A + L.card
  omega

theorem conjecture393b_intersection (_hG : G.Connected) (_horder : 2 < Fintype.card V) :
    twoDominationNumber G ≤ (remainder G).card + edgesOn G (supports G) +
      uniqueNeighborCount G (supports G) :=
  completion_b G (supports G)

end PendantTwoDominationProof

#print axioms PendantTwoDominationProof.completion_c
#print axioms PendantTwoDominationProof.conjecture393c_intersection
#print axioms PendantTwoDominationProof.card_high_degree_le_edges
#print axioms PendantTwoDominationProof.completion_b
#print axioms PendantTwoDominationProof.conjecture393b_intersection

