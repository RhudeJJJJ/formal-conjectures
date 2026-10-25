import Proofs.GraphicalBell.Base

namespace GraphicalBellProof
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V]

def singletons (S : Finset V) : Finset (Finset V) := S.image (fun x => {x})

lemma singletons_stable (G : SimpleGraph V) (S : Finset V) : StableOn G S (singletons S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    refine ⟨singleton_nonempty x, ?_⟩
    intro y hy z hz hyz
    have hy' : y = x := mem_singleton.mp hy
    have hz' : z = x := mem_singleton.mp hz
    exact (hyz (hy'.trans hz'.symm)).elim
  · intro B hb C hc hBC
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have hxy : x = y := (mem_singleton.mp hz).symm.trans (mem_singleton.mp hz')
    exact hBC (congrArg (fun w : V => ({w} : Finset V)) hxy)
  · ext x
    simp [singletons]

lemma singletons_card (S : Finset V) : (singletons S).card = S.card := by
  apply card_image_of_injective
  intro x y h
  change ({x} : Finset V) = {y} at h
  have hx : x ∈ ({y} : Finset V) := h ▸ mem_singleton_self x
  exact mem_singleton.mp hx

lemma complete_partition_unique {G : SimpleGraph V} {S : Finset V}
    (hc : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)
    {P : Finset (Finset V)} (hP : StableOn G S P) : P = singletons S := by
  have hblocks : ∀ B ∈ P, ∃ x ∈ S, B = {x} := by
    intro B hb
    obtain ⟨x, hx⟩ := (hP.1 B hb).1
    refine ⟨x, stable_subset hP hb hx, ?_⟩
    ext y
    constructor
    · intro hy
      apply mem_singleton.mpr
      by_contra hyx
      exact (hP.1 B hb).2 hy hx hyx
        (hc y (stable_subset hP hb hy) x (stable_subset hP hb hx) hyx)
    · intro hy
      simpa only [mem_singleton.mp hy] using hx
  apply Subset.antisymm
  · intro B hb
    obtain ⟨x, hx, rfl⟩ := hblocks B hb
    exact mem_image.mpr ⟨x, hx, rfl⟩
  · intro B hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    obtain ⟨C, hc', hxC⟩ := mem_biUnion.mp (show x ∈ P.biUnion id by rwa [hP.2.2])
    obtain ⟨y, hy, hCy⟩ := hblocks C hc'
    have hxy : x = y := by simpa [hCy] using hxC
    simpa [hCy, hxy] using hc'

lemma count_complete {G : SimpleGraph V} {S : Finset V}
    (hc : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) (k : ℕ) :
    count G S k = if k = S.card then 1 else 0 := by
  classical
  by_cases hk : k = S.card
  · subst k
    let : Unique (Graded G S S.card) :=
      { default := ⟨⟨singletons S, singletons_stable G S⟩, singletons_card S⟩
        uniq := fun P => Subtype.ext (Subtype.ext (complete_partition_unique hc P.val.property)) }
    simp [count]
  · let : IsEmpty (Graded G S k) := ⟨fun P => hk (by
      rw [← P.property, complete_partition_unique hc P.val.property, singletons_card])⟩
    simp [count, hk]

end GraphicalBellProof
