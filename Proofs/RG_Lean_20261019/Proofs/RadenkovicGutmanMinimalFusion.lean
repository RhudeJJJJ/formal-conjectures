/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOrderFour

/-!
# The first actual strict pendant-fusion case

Every admissible four-vertex source is the star, and its own fused graph is
the four-vertex path. Their exact energy drop is 3 - 2 sqrt(2) > 0.
Consequently strict fusion above five is equivalent to uniform strict fusion.
Neither of these equivalent unrestricted hypotheses is proved here.

This extends the source-bound order-four checkpoint in RG_ORDER_FOUR_20261020.
The actual source/fused definitions and both physical arm lengths are retained.
-/

namespace Gebendorfer.RadenkovicGutman.MinimalFusion

open SimpleGraph CoreQuotient RewireTopology GlobalAssembly FourVertexSpectrum
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem starFour_leaves : leafCount starFour = 3 := by
  have hc : starFour.degree 0 = 3 := by
    rw [starFour, degree_starGraph_center]
    norm_num
  have he : (Finset.univ.filter fun i : Fin 4 => starFour.degree i = 1) =
      Finset.univ.erase 0 := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [hc]
    · have hd : starFour.degree i = 1 := degree_starGraph_of_ne_center hi
      simp [hd, hi]
  unfold leafCount
  rw [he]
  norm_num

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Relabeling preserves the given source, rather than choosing a replacement graph. -/
theorem source_iso_star_four (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hn : Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) = 4) :
    Nonempty (source C u p q ≃g starFour) := by
  let S := V ⊕ Fin (p + 1) ⊕ Fin (q + 1)
  let e : Fin 4 ≃ S := (finCongr hn.symm).trans (Fintype.equivFin S).symm
  let T := (source C u p q).comap e
  let f : T ≃g source C u p q := Iso.comap e (source C u p q)
  have hp : ¬Nonempty (T ≃g pathGraph 4) := by
    rintro ⟨g⟩
    apply FusionTerminal.fusion_source_not_path C u p q hT hd
    rw [hn]
    exact ⟨f.symm.trans g⟩
  obtain ⟨g⟩ := OrderFour.nonpath_iso_starFour T (f.isTree_iff.mpr hT) hp
  exact ⟨f.symm.trans g⟩

/-- This is the actual fusion of the same source and the same two arms. -/
theorem fused_iso_path_four (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hn : Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) = 4) :
    Nonempty (fused C u p q ≃g pathGraph 4) := by
  obtain ⟨f⟩ := source_iso_star_four C u p q hT hd hn
  have hl : leafCount (source C u p q) = 3 :=
    (leaf_count_iso f).trans starFour_leaves
  have ht := FusionDescent.fusion_tree_and_leaf_count C u p q hT hd
  have hnF : Fintype.card (V ⊕ Fin (p + q + 2)) = 4 := ht.2.1.symm.trans hn
  have hp := FusionTerminal.three_leaf_fusion_is_path C u p q hT hd hl
  simp only [Fintype.card_sum, Fintype.card_fin] at hnF
  simpa only [Fintype.card_sum, Fintype.card_fin, hnF] using hp

theorem actual_energies_four (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hn : Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) = 4) :
    laplacianEnergy (source C u p q) = 5 ∧
      laplacianEnergy (fused C u p q) = 2 + 2 * Real.sqrt 2 := by
  obtain ⟨f⟩ := source_iso_star_four C u p q hT hd hn
  obtain ⟨g⟩ := fused_iso_path_four C u p q hT hd hn
  exact ⟨(energy_iso f).trans starFour_energy, (energy_iso g).trans pathFour_energy⟩

theorem exact_drop_four (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hn : Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) = 4) :
    laplacianEnergy (source C u p q) - laplacianEnergy (fused C u p q) =
      3 - 2 * Real.sqrt 2 := by
  obtain ⟨hs, hf⟩ := actual_energies_four C u p q hT hd hn
  rw [hs, hf]
  ring

theorem strictFusion_four (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hn : Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) = 4) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  obtain ⟨hs, hf⟩ := actual_energies_four C u p q hT hd hn
  rw [hs, hf]
  simpa only [pathFour_energy, starFour_energy] using pathFour_energy_lt_starFour

/-- The minimal admissible order forces two single-edge arms and a two-vertex core. -/
theorem minimal_parameters {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m)
    (p q : ℕ) (hd : 1 ≤ C.degree u)
    (hn : Fintype.card (Fin m ⊕ Fin (p + 1) ⊕ Fin (q + 1)) = 4) :
    m = 2 ∧ p = 0 ∧ q = 0 ∧ C.degree u = 1 := by
  have hm := C.degree_lt_card_verts u
  rw [Fintype.card_fin] at hm
  simp only [Fintype.card_sum, Fintype.card_fin] at hn
  omega

/-- All admissible orders below five are covered; no smaller admissible order exists. -/
theorem strictFusion_below_five {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m)
    (p q : ℕ) (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hn : Fintype.card (Fin m ⊕ Fin (p + 1) ⊕ Fin (q + 1)) < 5) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  have hmin := SmallOrders.four_le_source_order C u p q hd
  exact strictFusion_four C u p q hT hd (by omega)

/-- Raising any cutoff at most five to five removes only the now-proved finite case. -/
theorem strictFusionAbove_iff_five (N : ℕ) (hN : N ≤ 5) :
    StrictFusionAbove N ↔ StrictFusionAbove 5 := by
  constructor
  · intro h m C u p q hn hT hd
    exact h m C u p q (by omega) hT hd
  · intro h m C u p q _ hT hd
    by_cases hn : 5 ≤ Fintype.card (Fin m ⊕ Fin (p + 1) ⊕ Fin (q + 1))
    · exact h m C u p q hn hT hd
    · exact strictFusion_below_five C u p q hT hd (by omega)

theorem uniformStrictFusion_iff_cutoff_five :
    SmallOrders.UniformStrictFusion ↔ StrictFusionAbove 5 :=
  SmallOrders.uniformStrictFusion_iff_cutoff_four.trans
    (strictFusionAbove_iff_five 4 (by omega))

#check @strictFusion_four
#check @minimal_parameters
#check @strictFusionAbove_iff_five
#check @uniformStrictFusion_iff_cutoff_five

#print axioms starFour_leaves
#print axioms source_iso_star_four
#print axioms fused_iso_path_four
#print axioms actual_energies_four
#print axioms exact_drop_four
#print axioms strictFusion_four
#print axioms minimal_parameters
#print axioms strictFusion_below_five
#print axioms strictFusionAbove_iff_five
#print axioms uniformStrictFusion_iff_cutoff_five

end
end Gebendorfer.RadenkovicGutman.MinimalFusion
