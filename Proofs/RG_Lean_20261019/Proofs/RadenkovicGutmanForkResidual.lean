/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNonpathFork

/-!
# The actual residual graph after removing two pendant arms

Every neighbor of a nonroot arm vertex remains on that arm. The induced
residual retains the common root and at least one of its original neighbors.
This establishes the positive residual root-degree condition on the same
chosen arms. A labelled isomorphism to `CoreQuotient.source` is still required.
-/

namespace Gebendorfer.RadenkovicGutman.NonpathFork

open SimpleGraph
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A leaf-ended path with no branching away from its root has no side exits. -/
theorem path_nonroot_closed {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hpos : 0 < p.length) (hv : G.degree v = 1)
    (hd : ∀ x ∈ p.support, x ≠ u → G.degree x ≤ 2)
    {x y : V} (hx : x ∈ p.support) (hxu : x ≠ u) (hxy : G.Adj x y) :
    y ∈ p.support := by
  have hnil : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr hpos
  have hn : p.toSubgraph.neighborSet x = G.neighborSet x := by
    apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
    rw [Set.ncard_eq_toFinset_card', ← G.neighborFinset_def, card_neighborFinset_eq_degree]
    by_cases hxv : x = v
    · subst x
      rw [hp.neighborSet_toSubgraph_endpoint hnil, Set.ncard_singleton, hv]
    · obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      have hi0 : i ≠ 0 := by
        intro h
        subst i
        exact hxu (by simpa using hi.symm)
      have hilt : i < p.length := by
        by_contra h
        have he : i = p.length := by omega
        subst i
        exact hxv (by simpa using hi.symm)
      rw [← hi, hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt]
      exact hd x hx hxu
  exact p.mem_verts_toSubgraph.mp
    (p.toSubgraph.neighborSet_subset_verts x ((hn.symm) ▸ hxy))

def PendantFork.residualSet (F : PendantFork G) : Set V :=
  {x | x = F.root ∨ (x ∉ F.left.support ∧ x ∉ F.right.support)}

def PendantFork.residual (F : PendantFork G) : SimpleGraph F.residualSet :=
  G.induce F.residualSet

def PendantFork.residualRoot (F : PendantFork G) : F.residualSet :=
  ⟨F.root, Or.inl rfl⟩

theorem PendantFork.left_closed (F : PendantFork G) {x y : V}
    (hx : x ∈ F.left.support) (hxu : x ≠ F.root) (hxy : G.Adj x y) :
    y ∈ F.left.support :=
  path_nonroot_closed F.left F.left_path F.left_positive F.left_leaf
    F.left_unbranched hx hxu hxy

theorem PendantFork.right_closed (F : PendantFork G) {x y : V}
    (hx : x ∈ F.right.support) (hxu : x ≠ F.root) (hxy : G.Adj x y) :
    y ∈ F.right.support :=
  path_nonroot_closed F.right F.right_path F.right_positive F.right_leaf
    F.right_unbranched hx hxu hxy

/-- The third root neighbor is retained in the very residual induced by these arms. -/
theorem PendantFork.residual_root_neighbor (F : PendantFork G) (hT : G.IsTree) :
    ∃ z : F.residualSet, F.residual.Adj F.residualRoot z := by
  have hnot : ¬G.neighborFinset F.root ⊆ {F.left.snd, F.right.snd} := by
    intro h
    have hc := Finset.card_le_card h
    have hpair : ({F.left.snd, F.right.snd} : Finset V).card ≤ 2 :=
      Finset.card_le_two
    rw [card_neighborFinset_eq_degree] at hc
    have := F.root_degree
    omega
  obtain ⟨z, hz, hzne⟩ := Finset.not_subset.mp hnot
  have hadj : G.Adj F.root z := by simpa using hz
  have hzl : z ∉ F.left.support := by
    intro h
    exact hzne (by simp [hT.isAcyclic.eq_snd_of_adj_start F.left_path hadj h])
  have hzr : z ∉ F.right.support := by
    intro h
    exact hzne (by simp [hT.isAcyclic.eq_snd_of_adj_start F.right_path hadj h])
  exact ⟨⟨z, Or.inr ⟨hzl, hzr⟩⟩, hadj⟩

theorem PendantFork.residual_root_degree (F : PendantFork G) (hT : G.IsTree) :
    1 ≤ F.residual.degree F.residualRoot := by
  obtain ⟨z, hz⟩ := F.residual_root_neighbor hT
  exact Nat.succ_le_iff.mpr (degree_pos_iff_exists_adj.mpr ⟨z, hz⟩)

#print axioms path_nonroot_closed
#print axioms PendantFork.left_closed
#print axioms PendantFork.right_closed
#print axioms PendantFork.residual_root_neighbor
#print axioms PendantFork.residual_root_degree

end
end Gebendorfer.RadenkovicGutman.NonpathFork
