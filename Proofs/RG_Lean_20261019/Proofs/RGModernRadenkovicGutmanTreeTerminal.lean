module
/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
public import Proofs.RGModernRadenkovicGutmanRewireTopology
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

/-!
# The terminal trees for RG leaf descent

For a finite nontrivial tree, the leaf count is two plus the total degree excess.
Its leaf count is two precisely when it is isomorphic to the path of the same order.
The singleton tree is excluded from the leaf-count characterization.
-/

namespace Gebendorfer.RadenkovicGutman.TreeTerminal

open SimpleGraph RewireTopology
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V]

/-- The total branching excess, with natural subtraction at each vertex. -/
def branchingExcess (G : SimpleGraph V) : ℕ := ∑ v, (G.degree v - 2)

theorem leaf_count_eq_two_add_excess [Nontrivial V] (G : SimpleGraph V)
    (hT : G.IsTree) : leafCount G = 2 + branchingExcess G := by
  have hlocal : ∀ v, G.degree v + (if G.degree v = 1 then 1 else 0) =
      2 + (G.degree v - 2) := by
    intro v
    have hp := hT.connected.preconnected.degree_pos_of_nontrivial v
    split_ifs <;> omega
  have hs : (∑ v : V, (G.degree v + (if G.degree v = 1 then 1 else 0))) =
      ∑ v : V, (2 + (G.degree v - 2)) :=
    Finset.sum_congr rfl (fun v _ => hlocal v)
  have he := hT.card_edgeFinset
  have hd := G.sum_degrees_eq_twice_card_edges
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Finset.sum_boole] at hs
  change (∑ v, G.degree v) + leafCount G =
    Fintype.card V * 2 + branchingExcess G at hs
  omega

theorem branching_excess_eq_zero_iff (G : SimpleGraph V) :
    branchingExcess G = 0 ↔ ∀ v, G.degree v ≤ 2 := by
  simp [branchingExcess, Finset.sum_eq_zero_iff, Nat.sub_eq_zero_iff_le]

theorem leaf_count_eq_two_iff_degree_le_two [Nontrivial V] (G : SimpleGraph V)
    (hT : G.IsTree) : leafCount G = 2 ↔ ∀ v, G.degree v ≤ 2 := by
  rw [leaf_count_eq_two_add_excess G hT]
  simpa using branching_excess_eq_zero_iff G

theorem path_graph_degree_le_two (n : ℕ) (i : Fin n) : (pathGraph n).degree i ≤ 2 := by
  let f : (pathGraph n).neighborSet i → Fin 2 := fun j =>
    if j.val.val < i.val then 0 else 1
  have hf : Function.Injective f := by
    intro a b hab
    have ha := pathGraph_adj.mp a.property
    have hb := pathGraph_adj.mp b.property
    apply Subtype.ext
    apply Fin.ext
    dsimp [f] at hab
    split_ifs at hab <;> simp at hab <;> omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [card_neighborSet_eq_degree, Fintype.card_fin] using hc

/-- A path between two leaves exhausts a connected graph of maximum degree two. -/
theorem leaf_path_spanning (G : SimpleGraph V) (hG : G.Connected)
    (hd : ∀ v, G.degree v ≤ 2) {u v : V} (huv : u ≠ v)
    (hu : G.degree u = 1) (hv : G.degree v = 1)
    (p : G.Walk u v) (hp : p.IsPath) : p.toSubgraph.IsSpanning := by
  have hnil : ¬p.Nil := Walk.not_nil_of_ne huv
  have hn : ∀ x ∈ p.support, p.toSubgraph.neighborSet x = G.neighborSet x := by
    intro x hx
    apply Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset x)
    rw [Set.ncard_eq_toFinset_card', ← G.neighborFinset_def, card_neighborFinset_eq_degree]
    by_cases hxu : x = u
    · subst x
      rw [hp.neighborSet_toSubgraph_startpoint hnil, Set.ncard_singleton, hu]
    · by_cases hxv : x = v
      · subst x
        rw [hp.neighborSet_toSubgraph_endpoint hnil, Set.ncard_singleton, hv]
      · obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
        have hi0 : i ≠ 0 := by
          intro hz
          subst i
          exact hxu (by simpa using hi.symm)
        have hilt : i < p.length := by
          by_contra h
          have heq : i = p.length := by omega
          subst i
          exact hxv (by simpa using hi.symm)
        rw [← hi, hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt]
        exact hd _
  have hclosed : ∀ x y, x ∈ p.support → G.Adj x y → y ∈ p.support := by
    intro x y hx hxy
    apply p.mem_verts_toSubgraph.mp
    exact p.toSubgraph.neighborSet_subset_verts x ((hn x hx).symm ▸ hxy)
  have hwalk : ∀ {a b} (q : G.Walk a b), b ∈ p.support → a ∈ p.support := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hab q ih =>
      intro hb
      exact hclosed _ _ (ih hb) hab.symm
  intro x
  obtain ⟨q⟩ := hG x u
  exact p.mem_verts_toSubgraph.mpr (hwalk q p.start_mem_support)

/-- Every finite nontrivial tree of maximum degree two is the path of its order. -/
theorem tree_path_iso_of_degree_le_two [Nontrivial V] (G : SimpleGraph V)
    (hT : G.IsTree) (hd : ∀ v, G.degree v ≤ 2) :
    Nonempty (G ≃g pathGraph (Fintype.card V)) := by
  obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath u v
  have hs := leaf_path_spanning G hT.connected hd huv hu hv p hp
  let e := p.toSubgraph.spanningCoeEquivCoeOfSpanning hs
  have hc : p.toSubgraph.spanningCoe.Connected :=
    e.connected_iff.mpr p.toSubgraph_connected
  have heq : p.toSubgraph.spanningCoe = G :=
    le_antisymm p.toSubgraph.spanningCoe_le
      ((isTree_iff_minimal_connected.mp hT).2 hc p.toSubgraph.spanningCoe_le)
  have f : pathGraph (p.length + 1) ≃g G := by
    simpa only [heq] using hp.pathGraphIsoToSubgraph.trans e.symm
  have hcard : p.length + 1 = Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_congr f.toEquiv
  exact ⟨(hcard ▸ f).symm⟩

theorem tree_two_leaves_iff_path [Nontrivial V] (G : SimpleGraph V) (hT : G.IsTree) :
    leafCount G = 2 ↔ Nonempty (G ≃g pathGraph (Fintype.card V)) := by
  rw [leaf_count_eq_two_iff_degree_le_two G hT]
  refine ⟨tree_path_iso_of_degree_le_two G hT, ?_⟩
  rintro ⟨f⟩ v
  rw [← f.degree_eq v]
  exact path_graph_degree_le_two _ _

theorem nonpath_has_three_leaves [Nontrivial V] (G : SimpleGraph V) (hT : G.IsTree)
    (hpath : ¬Nonempty (G ≃g pathGraph (Fintype.card V))) : 3 ≤ leafCount G := by
  have hl := leaf_count_eq_two_add_excess G hT
  have hn := (tree_two_leaves_iff_path G hT).not.mpr hpath
  omega

#print axioms leaf_count_eq_two_add_excess
#print axioms branching_excess_eq_zero_iff
#print axioms leaf_count_eq_two_iff_degree_le_two
#print axioms path_graph_degree_le_two
#print axioms leaf_path_spanning
#print axioms tree_path_iso_of_degree_le_two
#print axioms tree_two_leaves_iff_path
#print axioms nonpath_has_three_leaves

end
end Gebendorfer.RadenkovicGutman.TreeTerminal
