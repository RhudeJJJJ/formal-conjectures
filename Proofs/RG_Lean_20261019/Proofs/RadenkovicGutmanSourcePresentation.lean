/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanArmEmbedding
import Proofs.RadenkovicGutmanGlobalAssembly

/-!
# Unconditional nonpath source presentation and two-input global assembly

Relabel the very residual and the two actual tail paths supplied by PendantFork.
The resulting source is isomorphic to the original graph, with the same root,
both attachment edges, and the physical arm lengths. This discharges the
`DecomposesAbove` predicate of the checked GlobalAssembly module for every cutoff.
Only finite coverage and strict fusion remain inputs to the global conclusions.
Sources: GlobalAssembly at 997d8d2931b45ea792aa12e812e2ae34153b086e and the
actual fork/residual at b546e3edbad3e45182649bc798182bf30a7457fe. The energy targets
follow PR #7399, statement commit 3654bf2bddc5217f904b7b85207b1091e833de49.
-/

namespace Gebendorfer.RadenkovicGutman.SourcePresentation

open SimpleGraph NonpathFork ArmEmbedding CoreQuotient GlobalAssembly
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def coreEquiv (F : PendantFork G) : Fin (Fintype.card F.residualSet) ≃ F.residualSet :=
  (Fintype.equivFin F.residualSet).symm

def core (F : PendantFork G) : SimpleGraph (Fin (Fintype.card F.residualSet)) :=
  F.residual.comap (coreEquiv F)

def coreRoot (F : PendantFork G) : Fin (Fintype.card F.residualSet) :=
  (coreEquiv F).symm F.residualRoot

theorem coreRoot_value (F : PendantFork G) : ((coreEquiv F) (coreRoot F)).val = F.root := by
  simp [coreRoot, PendantFork.residualRoot]

theorem core_value_eq_root_iff (F : PendantFork G) (c : Fin (Fintype.card F.residualSet)) :
    ((coreEquiv F) c).val = F.root ↔ c = coreRoot F := by
  constructor
  · intro h
    apply (coreEquiv F).injective
    apply Subtype.ext
    simpa only [coreRoot_value] using h
  · rintro rfl
    exact coreRoot_value F

theorem core_tree (F : PendantFork G) (hT : G.IsTree) : (core F).IsTree :=
  (Iso.comap (coreEquiv F) F.residual).isTree_iff.mpr (F.residual_tree hT)

theorem core_root_degree (F : PendantFork G) (hT : G.IsTree) : 1 ≤ (core F).degree (coreRoot F) := by
  obtain ⟨z, hz⟩ := F.residual_root_neighbor hT
  have hadj : (core F).Adj (coreRoot F) ((coreEquiv F).symm z) := by
    change F.residual.Adj ((coreEquiv F) ((coreEquiv F).symm F.residualRoot))
      ((coreEquiv F) ((coreEquiv F).symm z))
    simpa only [Equiv.apply_symm_apply] using hz
  exact Nat.succ_le_iff.mpr hadj.degree_pos_left

theorem left_not_residual (F : PendantFork G) (i : Fin (F.left.tail.length + 1)) :
    armVertex F.left i ∉ F.residualSet := by
  rintro (h | h)
  · exact armVertex_ne_root F.left F.left_path F.left_positive i h
  · exact h.1 (armVertex_mem F.left F.left_path F.left_positive i)

theorem right_not_residual (F : PendantFork G) (i : Fin (F.right.tail.length + 1)) :
    armVertex F.right i ∉ F.residualSet := by
  rintro (h | h)
  · exact armVertex_ne_root F.right F.right_path F.right_positive i h
  · exact h.2 (armVertex_mem F.right F.right_path F.right_positive i)

theorem core_ne_left (F : PendantFork G) (c : Fin (Fintype.card F.residualSet))
    (i : Fin (F.left.tail.length + 1)) : ((coreEquiv F) c).val ≠ armVertex F.left i := by
  intro h
  apply left_not_residual F i
  rw [← h]
  exact ((coreEquiv F) c).property

theorem core_ne_right (F : PendantFork G) (c : Fin (Fintype.card F.residualSet))
    (i : Fin (F.right.tail.length + 1)) : ((coreEquiv F) c).val ≠ armVertex F.right i := by
  intro h
  apply right_not_residual F i
  rw [← h]
  exact ((coreEquiv F) c).property

theorem arms_ne (F : PendantFork G) (i : Fin (F.left.tail.length + 1))
    (j : Fin (F.right.tail.length + 1)) : armVertex F.left i ≠ armVertex F.right j := by
  intro h
  have hr : armVertex F.left i ∈ F.right.support := by
    rw [h]
    exact armVertex_mem F.right F.right_path F.right_positive j
  exact armVertex_ne_root F.left F.left_path F.left_positive i
    (F.intersection _ (armVertex_mem F.left F.left_path F.left_positive i) hr)

def vertexMap (F : PendantFork G) :
    Fin (Fintype.card F.residualSet) ⊕ Fin (F.left.tail.length + 1) ⊕
      Fin (F.right.tail.length + 1) → V
  | .inl c => ((coreEquiv F) c).val
  | .inr (.inl i) => armVertex F.left i
  | .inr (.inr j) => armVertex F.right j

theorem vertexMap_injective (F : PendantFork G) : Function.Injective (vertexMap F) := by
  intro x y h
  rcases x with c | (i | j) <;> rcases y with d | (k | l) <;> dsimp [vertexMap] at h
  · exact congrArg Sum.inl ((coreEquiv F).injective (Subtype.ext h))
  · exact (core_ne_left F c k h).elim
  · exact (core_ne_right F c l h).elim
  · exact (core_ne_left F d i h.symm).elim
  · exact congrArg (fun a => Sum.inr (Sum.inl a)) (armVertex_injective F.left F.left_path h)
  · exact (arms_ne F i l h).elim
  · exact (core_ne_right F d j h.symm).elim
  · exact (arms_ne F k j h.symm).elim
  · exact congrArg (fun a => Sum.inr (Sum.inr a)) (armVertex_injective F.right F.right_path h)

theorem vertexMap_surjective (F : PendantFork G) : Function.Surjective (vertexMap F) := by
  intro x
  by_cases hx : x ∈ F.residualSet
  · refine ⟨.inl ((coreEquiv F).symm ⟨x, hx⟩), ?_⟩
    simp [vertexMap]
  · have hxu : x ≠ F.root := fun h => hx (Or.inl h)
    by_cases hl : x ∈ F.left.support
    · obtain ⟨i, hi⟩ := armVertex_range F.left F.left_path F.left_positive hl hxu
      exact ⟨.inr (.inl i), hi⟩
    · have hr : x ∈ F.right.support := by
        by_contra hr
        exact hx (Or.inr ⟨hl, hr⟩)
      obtain ⟨j, hj⟩ := armVertex_range F.right F.right_path F.right_positive hr hxu
      exact ⟨.inr (.inr j), hj⟩

def vertexEquiv (F : PendantFork G) :
    (Fin (Fintype.card F.residualSet) ⊕ Fin (F.left.tail.length + 1) ⊕
      Fin (F.right.tail.length + 1)) ≃ V :=
  Equiv.ofBijective (vertexMap F) ⟨vertexMap_injective F, vertexMap_surjective F⟩

theorem core_arm_adj_iff (F : PendantFork G) (hT : G.IsTree) {v : V}
    (p : G.Walk F.root v) (hp : p.IsPath) (hpos : 0 < p.length)
    (hnot : ∀ i, armVertex p i ∉ F.residualSet)
    (c : Fin (Fintype.card F.residualSet)) (i : Fin (p.tail.length + 1)) :
    G.Adj ((coreEquiv F) c).val (armVertex p i) ↔ c = coreRoot F ∧ i = 0 := by
  constructor
  · intro h
    have he : ((coreEquiv F) c).val = F.root :=
      F.residual_boundary (hnot i) ((coreEquiv F) c).property h.symm
    refine ⟨(core_value_eq_root_iff F c).mp he, ?_⟩
    exact (root_arm_adj_iff hT.isAcyclic p hp hpos i).mp (by simpa only [he] using h)
  · rintro ⟨rfl, rfl⟩
    rw [coreRoot_value]
    exact (root_arm_adj_iff hT.isAcyclic p hp hpos 0).mpr rfl

theorem no_cross_arm_adj (F : PendantFork G) (i : Fin (F.left.tail.length + 1))
    (j : Fin (F.right.tail.length + 1)) : ¬G.Adj (armVertex F.left i) (armVertex F.right j) := by
  intro h
  have hr := F.left_closed (armVertex_mem F.left F.left_path F.left_positive i)
    (armVertex_ne_root F.left F.left_path F.left_positive i) h
  exact armVertex_ne_root F.right F.right_path F.right_positive j
    (F.intersection _ hr (armVertex_mem F.right F.right_path F.right_positive j))

/-- The source uses the same residual, root and physical arms, including single-edge arms. -/
def sourceIso (F : PendantFork G) (hT : G.IsTree) :
    source (core F) (coreRoot F) F.left.tail.length F.right.tail.length ≃g G where
  toEquiv := vertexEquiv F
  map_rel_iff' := by
    intro x y
    change G.Adj (vertexMap F x) (vertexMap F y) ↔ _
    rcases x with c | (i | j) <;> rcases y with d | (k | l)
    · simp [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap, core, PendantFork.residual]
    · simpa [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap] using
        core_arm_adj_iff F hT F.left F.left_path F.left_positive (left_not_residual F) c k
    · simpa [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap] using
        core_arm_adj_iff F hT F.right F.right_path F.right_positive (right_not_residual F) c l
    · simpa [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap, adj_comm] using
        core_arm_adj_iff F hT F.left F.left_path F.left_positive (left_not_residual F) d i
    · simpa [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap] using
        armVertex_adj_iff hT.isAcyclic F.left F.left_path i k
    · simp [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap, no_cross_arm_adj]
    · simpa [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap, adj_comm] using
        core_arm_adj_iff F hT F.right F.right_path F.right_positive (right_not_residual F) d j
    · simp [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap, adj_comm, no_cross_arm_adj]
    · simpa [source, joinTwo, SimpleGraph.sum, edge_adj, vertexMap] using
        armVertex_adj_iff hT.isAcyclic F.right F.right_path j l

theorem physical_arm_lengths (F : PendantFork G) :
    F.left.tail.length + 1 = F.left.length ∧ F.right.tail.length + 1 = F.right.length :=
  ⟨Walk.length_tail_add_one (Walk.not_nil_iff_lt_length.mpr F.left_positive),
    Walk.length_tail_add_one (Walk.not_nil_iff_lt_length.mpr F.right_positive)⟩

/-- Every finite nontrivial nonpath tree has an admissible actual source presentation. -/
theorem nonpath_source [Nontrivial V] (hT : G.IsTree)
    (hpath : ¬Nonempty (G ≃g pathGraph (Fintype.card V))) :
    ∃ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
      C.IsTree ∧ 1 ≤ C.degree u ∧ Nonempty (G ≃g source C u p q) := by
  obtain ⟨F⟩ := nonpath_has_pendant_fork hT hpath
  exact ⟨Fintype.card F.residualSet, core F, coreRoot F, F.left.tail.length,
    F.right.tail.length, core_tree F hT, core_root_degree F hT, ⟨(sourceIso F hT).symm⟩⟩

/-- The decomposition input is discharged for every natural order cutoff. -/
theorem decomposesAbove (N : ℕ) : DecomposesAbove N := by
  intro n _ T hT hpath
  by_cases hn : 2 ≤ n
  · let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    have hp : ¬Nonempty (T ≃g pathGraph (Fintype.card (Fin n))) := by
      simpa only [Fintype.card_fin] using hpath
    obtain ⟨m, C, u, p, q, _, hd, hf⟩ := nonpath_source hT hp
    exact ⟨m, C, u, p, q, hd, hf⟩
  · have hpos : 0 < n := by
      obtain ⟨v⟩ := hT.connected.nonempty
      exact lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
    have hn1 : n = 1 := by omega
    subst n
    have heq : T = pathGraph 1 := by
      ext u v
      have he : v = u := Subsingleton.elim _ _
      subst v
      simp
    exact (hpath (by rw [heq]; exact ⟨Iso.refl⟩)).elim

/-- Finite coverage and strict fusion are the only remaining inputs to the global target. -/
theorem universal_conclusion_of_inputs (N : ℕ) (hsmall : SmallOrders N)
    (hF : StrictFusionAbove N) (n : ℕ) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) : Conclusion T :=
  universal_conclusion N hsmall (decomposesAbove N) hF n hn T hT

theorem path_minimum_of_inputs (N : ℕ) (hsmall : SmallOrders N)
    (hF : StrictFusionAbove N) (n : ℕ) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    laplacianEnergy (pathGraph n) ≤ laplacianEnergy T :=
  (universal_conclusion_of_inputs N hsmall hF n hn T hT).1

theorem path_equality_of_inputs (N : ℕ) (hsmall : SmallOrders N)
    (hF : StrictFusionAbove N) (n : ℕ) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    laplacianEnergy T = laplacianEnergy (pathGraph n) ↔ Nonempty (T ≃g pathGraph n) :=
  (universal_conclusion_of_inputs N hsmall hF n hn T hT).2

#print axioms coreRoot_value
#print axioms core_value_eq_root_iff
#print axioms core_tree
#print axioms core_root_degree
#print axioms left_not_residual
#print axioms right_not_residual
#print axioms core_ne_left
#print axioms core_ne_right
#print axioms arms_ne
#print axioms vertexMap_injective
#print axioms vertexMap_surjective
#print axioms vertexEquiv
#print axioms core_arm_adj_iff
#print axioms no_cross_arm_adj
#print axioms sourceIso
#print axioms physical_arm_lengths
#print axioms nonpath_source
#print axioms decomposesAbove
#print axioms universal_conclusion_of_inputs
#print axioms path_minimum_of_inputs
#print axioms path_equality_of_inputs

#check @decomposesAbove
#check @universal_conclusion_of_inputs
#check @path_minimum_of_inputs
#check @path_equality_of_inputs

end
end Gebendorfer.RadenkovicGutman.SourcePresentation
