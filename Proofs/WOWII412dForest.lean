import Proofs.WOWII412dCore
import Proofs.StrictHallForest

/-!
# A selected forest on the core for WOWII 412d

Source: Gebendorfer, 11 October 2026, Lemmas 4(3) and 5.
This closes the indexed pair-selection step from the actual core/excluded
neighborhoods. The bounded cover is proved separately in WOWII412dCover.
This module records the forest selection itself.
-/
namespace WOWII412dCore
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The strict Hall selection is realized by actual neighbors in the core.
No two excluded vertices produce the same unordered edge. -/
theorem exists_core_forest (A : Finset V) (hA : Bipartition G A) :
    ∃ f p : {b // b ∈ univ \ corona G} → V,
      ∃ hpf : ∀ b, p b ≠ f b,
      Function.Injective f ∧
      (∀ b, f b ∈ core G ∧ p b ∈ core G ∧ G.Adj b.val (f b) ∧ G.Adj b.val (p b)) ∧
      (StrictHallForest.selectionGraph f p hpf).IsAcyclic ∧
      Function.Injective (fun b => s(f b, p b)) := by
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
    have hneX : X.Nonempty := hne.image _
    have he : S.biUnion E = neighbors G X ∩ core G := by
      ext w
      simp only [E, neighbors, mem_biUnion, mem_inter, mem_filter, mem_univ,
        true_and, mem_singleton, exists_eq_left, X, mem_image]
      aesop
    have hc := strict_neighbors G A X hA hX hneX
    have hxcard : X.card = S.card := card_image_of_injective S Subtype.val_injective
    rw [hxcard, ← he] at hc
    exact hc
  obtain ⟨f, p, hpf, hf, hmem, hforest, hedge⟩ :=
    StrictHallForest.exists_forest_selection E hHall
  refine ⟨f, p, hpf, hf, ?_, hforest, hedge⟩
  intro b
  obtain ⟨hfb, hpb⟩ := hmem b
  have hfn : G.Adj b.val (f b) := by
    simpa [E, neighbors] using (mem_inter.mp hfb).1
  have hpn : G.Adj b.val (p b) := by
    simpa [E, neighbors] using (mem_inter.mp hpb).1
  exact ⟨(mem_inter.mp hfb).2, (mem_inter.mp hpb).2, hfn, hpn⟩

end WOWII412dCore
