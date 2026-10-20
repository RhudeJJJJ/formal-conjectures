/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSourcePresentation

/-!
# The exact small-order basis for RG assembly

Every tree of order two or three is a path. Together with the checked singleton
case, this proves both energy conclusions at every positive order below four.
The global conclusion at cutoff four therefore requires only strict fusion.
This does not establish strict fusion or finite coverage at a larger cutoff.
-/

namespace Gebendorfer.RadenkovicGutman.SmallOrders

open SimpleGraph CoreQuotient TreeTerminal GlobalAssembly
open scoped Classical
noncomputable section

theorem tree_path_iso_below_four {n : ℕ} (hn : 2 ≤ n) (hn4 : n < 4)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Nonempty (T ≃g pathGraph n) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hd : ∀ v, T.degree v ≤ 2 := by
    intro v
    have hv := T.degree_lt_card_verts v
    rw [Fintype.card_fin] at hv
    omega
  have hp := tree_path_iso_of_degree_le_two T hT hd
  rw [Fintype.card_fin] at hp
  exact hp

/-- Exhaustive coverage of the exact finite base range 2 <= n < 4. -/
theorem smallOrders_four : GlobalAssembly.SmallOrders 4 := by
  intro n hn hn4 T hT
  obtain ⟨f⟩ := tree_path_iso_below_four hn hn4 T hT
  exact conclusion_of_iso T f

theorem smallOrders_of_le_four {N : ℕ} (hN : N ≤ 4) : GlobalAssembly.SmallOrders N := by
  intro n hn hnN T hT
  exact smallOrders_four n hn (by omega) T hT

/-- At an arbitrary cutoff, the only remaining finite cases start at order four. -/
theorem smallOrders_iff_from_four (N : ℕ) :
    GlobalAssembly.SmallOrders N ↔
      ∀ n, 4 ≤ n → n < N → ∀ T : SimpleGraph (Fin n), T.IsTree → Conclusion T := by
  constructor
  · intro h n hn hnN T hT
    exact h n (by omega) hnN T hT
  · intro h n hn hnN T hT
    by_cases hn4 : n < 4
    · exact smallOrders_four n hn hn4 T hT
    · exact h n (by omega) hnN T hT

/-- Positive core root degree forces every admissible source to have order at least four. -/
theorem four_le_source_order {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m)
    (p q : ℕ) (hu : 1 ≤ C.degree u) :
    4 ≤ Fintype.card (Fin m ⊕ Fin (p + 1) ⊕ Fin (q + 1)) := by
  have hm := C.degree_lt_card_verts u
  rw [Fintype.card_fin] at hm
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Strict decrease on every actual admissible source/fused pair, with no order cutoff. -/
def UniformStrictFusion : Prop :=
  ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → 1 ≤ C.degree u →
      laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q)

theorem uniformStrictFusion_iff_cutoff_four :
    UniformStrictFusion ↔ StrictFusionAbove 4 := by
  constructor
  · intro h m C u p q _ hT hu
    exact h m C u p q hT hu
  · intro h m C u p q hT hu
    exact h m C u p q (four_le_source_order C u p q hu) hT hu

/-- A conditional global reduction with strict fusion at the fixed cutoff four as its sole input. -/
theorem universal_conclusion_of_strictFusion_four (hF : StrictFusionAbove 4)
    (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Conclusion T :=
  SourcePresentation.universal_conclusion_of_inputs 4 smallOrders_four hF n hn T hT

theorem path_minimum_of_strictFusion_four (hF : StrictFusionAbove 4)
    (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    laplacianEnergy (pathGraph n) ≤ laplacianEnergy T :=
  (universal_conclusion_of_strictFusion_four hF n hn T hT).1

theorem path_equality_of_strictFusion_four (hF : StrictFusionAbove 4)
    (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    laplacianEnergy T = laplacianEnergy (pathGraph n) ↔ Nonempty (T ≃g pathGraph n) :=
  (universal_conclusion_of_strictFusion_four hF n hn T hT).2

theorem universal_conclusion_of_uniformStrictFusion (hF : UniformStrictFusion)
    (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Conclusion T :=
  universal_conclusion_of_strictFusion_four (uniformStrictFusion_iff_cutoff_four.mp hF) n hn T hT

#check @SimpleGraph.degree_lt_card_verts
#check @smallOrders_four
#check @smallOrders_iff_from_four
#check @universal_conclusion_of_strictFusion_four
#check @path_minimum_of_strictFusion_four
#check @path_equality_of_strictFusion_four

#print axioms tree_path_iso_below_four
#print axioms smallOrders_four
#print axioms smallOrders_of_le_four
#print axioms smallOrders_iff_from_four
#print axioms four_le_source_order
#print axioms uniformStrictFusion_iff_cutoff_four
#print axioms universal_conclusion_of_strictFusion_four
#print axioms path_minimum_of_strictFusion_four
#print axioms path_equality_of_strictFusion_four
#print axioms universal_conclusion_of_uniformStrictFusion

end
end Gebendorfer.RadenkovicGutman.SmallOrders
