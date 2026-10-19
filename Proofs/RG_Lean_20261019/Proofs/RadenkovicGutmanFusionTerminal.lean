/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFusionDescent
import Proofs.RadenkovicGutmanTreeTerminal

/-!
# The final step of RG leaf descent

An actual RG fusion consumes exactly one unit of branching excess.
If the source tree has three leaves, its fused tree is the path of the same order.
This does not assert existence of a source presentation for an arbitrary tree.
-/

namespace Gebendorfer.RadenkovicGutman.FusionTerminal

open SimpleGraph CoreQuotient RewireTopology FusionDescent TreeTerminal
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V]

/-- The branching excess is reduced by exactly one by the actual fusion. -/
theorem fusion_branching_excess (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) :
    branchingExcess (source C u p q) = branchingExcess (fused C u p q) + 1 := by
  letI : Nontrivial (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) :=
    ⟨⟨.inl u, .inr (.inl 0), by simp⟩⟩
  letI : Nontrivial (V ⊕ Fin (p + q + 2)) :=
    ⟨⟨.inl u, .inr 0, by simp⟩⟩
  have hF := fusion_tree_and_leaf_count C u p q hT hd
  have hS := leaf_count_eq_two_add_excess _ hT
  have hB := leaf_count_eq_two_add_excess _ hF.1
  have hl := hF.2.2
  omega

/-- A source tree with positive residual root degree cannot already be a path. -/
theorem fusion_source_not_path (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u) :
    ¬Nonempty (source C u p q ≃g pathGraph
      (Fintype.card (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)))) := by
  letI : Nontrivial (V ⊕ Fin (p + 1) ⊕ Fin (q + 1)) :=
    ⟨⟨.inl u, .inr (.inl 0), by simp⟩⟩
  intro hpath
  have hl := (tree_two_leaves_iff_path _ hT).mpr hpath
  have he := fusion_branching_excess C u p q hT hd
  have hs := leaf_count_eq_two_add_excess _ hT
  omega

/-- With three source leaves, the actual fused graph is the path of its order. -/
theorem three_leaf_fusion_is_path (C : SimpleGraph V) (u : V) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 1 ≤ C.degree u)
    (hl : leafCount (source C u p q) = 3) :
    Nonempty (fused C u p q ≃g pathGraph (Fintype.card (V ⊕ Fin (p + q + 2)))) := by
  letI : Nontrivial (V ⊕ Fin (p + q + 2)) :=
    ⟨⟨.inl u, .inr 0, by simp⟩⟩
  have hF := fusion_tree_and_leaf_count C u p q hT hd
  apply (tree_two_leaves_iff_path _ hF.1).mp
  have he := hF.2.2
  omega

#print axioms fusion_branching_excess
#print axioms fusion_source_not_path
#print axioms three_leaf_fusion_is_path

end
end Gebendorfer.RadenkovicGutman.FusionTerminal
