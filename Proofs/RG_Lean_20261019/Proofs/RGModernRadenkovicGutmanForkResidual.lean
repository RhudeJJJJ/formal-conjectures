module
/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
public import Proofs.RGModernRadenkovicGutmanNonpathFork

@[expose] public section

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
      have hc : (p.toSubgraph.neighborSet x).ncard = 2 := by
        rw [← hi]
        exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
      rw [hc]
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
  exact Nat.succ_le_iff.mpr hz.degree_pos_left

/-- The only possible boundary vertex of either removed arm is its common root. -/
theorem PendantFork.residual_boundary (F : PendantFork G) {x y : V}
    (hx : x ∉ F.residualSet) (hy : y ∈ F.residualSet) (hxy : G.Adj x y) :
    y = F.root := by
  have hxu : x ≠ F.root := fun h => hx (Or.inl h)
  have hmem : x ∈ F.left.support ∨ x ∈ F.right.support := by
    by_contra h
    exact hx (Or.inr ⟨fun hl => h (Or.inl hl), fun hr => h (Or.inr hr)⟩)
  rcases hy with hy | hy
  · exact hy
  · rcases hmem with hl | hr
    · exact (hy.1 (F.left_closed hl hxu hxy)).elim
    · exact (hy.2 (F.right_closed hr hxu hxy)).elim

/-- Collapse the selected arms to their common root and retain all residual labels. -/
def PendantFork.retract (F : PendantFork G) (x : V) : F.residualSet :=
  if hx : x ∈ F.residualSet then ⟨x, hx⟩ else F.residualRoot

theorem PendantFork.residual_connected (F : PendantFork G) (hT : G.IsTree) :
    F.residual.Connected := by
  have hstep : ∀ {x y}, G.Adj x y →
      F.residual.Reachable (F.retract x) (F.retract y) := by
    intro x y hxy
    by_cases hx : x ∈ F.residualSet
    · by_cases hy : y ∈ F.residualSet
      · have hadj : F.residual.Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
        simpa only [PendantFork.retract, dif_pos hx, dif_pos hy] using hadj.reachable
      · have he : (⟨x, hx⟩ : F.residualSet) = F.residualRoot :=
          Subtype.ext (F.residual_boundary hy hx hxy.symm)
        simpa only [PendantFork.retract, dif_pos hx, dif_neg hy, he] using
          (Reachable.rfl : F.residual.Reachable F.residualRoot F.residualRoot)
    · by_cases hy : y ∈ F.residualSet
      · have he : (⟨y, hy⟩ : F.residualSet) = F.residualRoot :=
          Subtype.ext (F.residual_boundary hx hy hxy)
        simpa only [PendantFork.retract, dif_neg hx, dif_pos hy, he] using
          (Reachable.rfl : F.residual.Reachable F.residualRoot F.residualRoot)
      · simp only [PendantFork.retract, dif_neg hx, dif_neg hy]
        exact Reachable.rfl
  have hwalk : ∀ {x y} (p : G.Walk x y),
      F.residual.Reachable (F.retract x) (F.retract y) := by
    intro x y p
    induction p with
    | nil => exact Reachable.rfl
    | cons h p ih => exact (hstep h).trans ih
  let : Nonempty F.residualSet := ⟨F.residualRoot⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨p⟩ := hT.connected x.val y.val
  simpa only [PendantFork.retract, dif_pos x.property, dif_pos y.property] using hwalk p

theorem PendantFork.residual_tree (F : PendantFork G) (hT : G.IsTree) :
    F.residual.IsTree :=
  ⟨F.residual_connected hT, hT.isAcyclic.induce F.residualSet⟩

/-- The selected arms and their own admissible residual exist without spectral assumptions. -/
theorem nonpath_fork_with_residual [Nontrivial V] (hT : G.IsTree)
    (hpath : ¬Nonempty (G ≃g pathGraph (Fintype.card V))) :
    ∃ F : PendantFork G, F.residual.IsTree ∧ 1 ≤ F.residual.degree F.residualRoot := by
  obtain ⟨F⟩ := nonpath_has_pendant_fork hT hpath
  exact ⟨F, F.residual_tree hT, F.residual_root_degree hT⟩

#print axioms path_nonroot_closed
#print axioms PendantFork.left_closed
#print axioms PendantFork.right_closed
#print axioms PendantFork.residual_root_neighbor
#print axioms PendantFork.residual_root_degree
#print axioms PendantFork.residual_boundary
#print axioms PendantFork.residual_connected
#print axioms PendantFork.residual_tree
#print axioms nonpath_fork_with_residual

end
end Gebendorfer.RadenkovicGutman.NonpathFork
