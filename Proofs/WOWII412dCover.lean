import Proofs.WOWII412dAssembly
import Proofs.RankedForestCover

/-!
# A bounded cover of the core and the excluded vertices

Source: Gebendorfer's WOWII 412d manuscript, 11 October 2026.
The strict Hall reduction is reused. The remaining incidence-cover step is
proved by a decreasing rank and simultaneous vertex/edge covers of its forest.
-/
namespace WOWII412dCore
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The core and its excluded neighbors have a total cover of size at most
that of the core. This discharges the hypothesis in the assembly reduction. -/
theorem exists_core_cover (A : Finset V) (hA : Bipartition G A)
    (hni : ∀ v, ∃ w, G.Adj v w) :
    ∃ D₀ : Finset V,
      (∀ v ∈ core G ∪ (univ \ corona G), ∃ w ∈ D₀, G.Adj v w) ∧
      D₀.card ≤ (core G).card := by
  classical
  let I := {b // b ∈ univ \ corona G}
  let E : I → Finset V := fun b => neighbors G {b.val} ∩ core G
  have hHall (S : Finset I) (hne : S.Nonempty) :
      S.card + 1 ≤ (S.biUnion E).card := by
    let X : Finset V := S.image Subtype.val
    have hX : X ⊆ univ \ corona G := by
      intro b hb
      obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      exact i.property
    have he : S.biUnion E = neighbors G X ∩ core G := by
      ext w
      simp only [E, neighbors, mem_biUnion, mem_inter, mem_filter, mem_univ,
        true_and, mem_singleton, exists_eq_left, X, mem_image]
      aesop
    have hc := strict_neighbors G A X hA hX (hne.image _)
    have hxcard : X.card = S.card := card_image_of_injective S Subtype.val_injective
    rw [hxcard, ← he] at hc
    exact hc
  have hEW : ∀ b, E b ⊆ core G := fun _ => inter_subset_right
  have hcover : ∀ w ∈ core G, ∃ b : I, w ∈ E b := by
    intro w hw
    obtain ⟨b, hwb⟩ := hni w
    have hb : b ∈ univ \ corona G := by
      rw [← neighbors_core_eq G A hA]
      exact mem_filter.mpr ⟨mem_univ _, w, hw, hwb⟩
    refine ⟨⟨b, hb⟩, mem_inter.mpr ⟨?_, hw⟩⟩
    simpa [neighbors] using hwb.symm
  obtain ⟨C, J, _hC, hCJ, hJC, hcard⟩ :=
    StrictHallForest.exists_incidence_cover E (core G) hHall hEW hcover
  refine ⟨C ∪ J.image Subtype.val, ?_, ?_⟩
  · intro v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨b, hb, hvb⟩ := hJC v hv
      refine ⟨b.val, mem_union_right _ (mem_image.mpr ⟨b, hb, rfl⟩), ?_⟩
      have h : G.Adj b.val v := by
        simpa [E, neighbors] using (mem_inter.mp hvb).1
      exact h.symm
    · obtain ⟨w, hw, hwb⟩ := hCJ ⟨v, hv⟩
      refine ⟨w, mem_union_left _ hw, ?_⟩
      simpa [E, neighbors] using (mem_inter.mp hwb).1
  · exact (card_union_le _ _).trans
      ((Nat.add_le_add_left (card_image_le) _).trans hcard)

/-- The complete strengthened total-domination bound. -/
theorem total_bound (hb : G.IsBipartite) (hni : ∀ v, ∃ w, G.Adj v w) :
    G.totalDominationNumber ≤ (criticalUnion G).card := by
  obtain ⟨A, hA⟩ := exists_bipartition G hb
  obtain ⟨D₀, hD, hc⟩ := exists_core_cover G A hA hni
  exact total_bound_of_core_cover G hb D₀ hD hc

end WOWII412dCore
