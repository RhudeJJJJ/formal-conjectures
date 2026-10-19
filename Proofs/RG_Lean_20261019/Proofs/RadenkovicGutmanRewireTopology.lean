/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Tree preservation and leaf descent for pendant-path fusion

The base graph omits the edge from the branching root `u` to the second arm `w`.
Fusion replaces that edge by the edge from the first arm's endpoint `v` to `w`.
All statements use the original labelled vertex set.
-/

namespace Gebendorfer.RadenkovicGutman.RewireTopology

open SimpleGraph
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V]

/-- Transport a walk by replacing each of its edges with a reachable pair. -/
omit [Fintype V] in
theorem reachable_transfer (G H : SimpleGraph V)
    (h : ∀ {x y}, G.Adj x y → H.Reachable x y) {x y : V}
    (hxy : G.Reachable x y) : H.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.rfl
  | cons ha p ih => exact (h ha).trans ih

/-- Moving one bridge attachment within its component preserves connectedness. -/
omit [Fintype V] in
theorem connected_rewire (G : SimpleGraph V) (u v w : V) (hvw : v ≠ w)
    (huv : G.Reachable u v) (hG : (G ⊔ edge u w).Connected) :
    (G ⊔ edge v w).Connected := by
  let H := G ⊔ edge v w
  have hvw' : H.Reachable v w :=
    (show H.Adj v w from Or.inr (by simp [edge_adj, hvw])).reachable
  have huw : H.Reachable u w := (huv.mono le_sup_left).trans hvw'
  letI : Nonempty V := ⟨u⟩
  refine ⟨fun x y => reachable_transfer _ H ?_ (hG x y)⟩
  intro a b hab
  rcases hab with hab | hab
  · exact (show H.Adj a b from Or.inl hab).reachable
  · rcases (edge_adj _ _ |>.mp hab).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huw
    · exact huw.symm

/-- The deleted and inserted edges are both new to the same base graph. -/
theorem edge_count_rewire (G : SimpleGraph V) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w) (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w) :
    (G ⊔ edge u w).edgeFinset.card = (G ⊔ edge v w).edgeFinset.card := by
  rw [G.card_edgeFinset_sup_edge hguw huw, G.card_edgeFinset_sup_edge hgvw hvw]

/-- The actual rewiring preserves the tree property, with no spectral premise. -/
theorem tree_rewire (G : SimpleGraph V) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w) (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w)
    (huv : G.Reachable u v) (hG : (G ⊔ edge u w).IsTree) :
    (G ⊔ edge v w).IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨connected_rewire G u v w hvw huv hG.connected, ?_⟩
  have hc := (isTree_iff_connected_and_card.mp hG).2
  have he := edge_count_rewire G u v w huw hvw hguw hgvw
  simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card, ← he] using hc

theorem degree_edge (u w x : V) (huw : u ≠ w) :
    (edge u w).degree x = if x = u ∨ x = w then 1 else 0 := by
  have hnu : (edge u w).neighborFinset u = {w} := by
    ext y
    simp only [mem_neighborFinset, edge_adj, Finset.mem_singleton]
    aesop
  have hnw : (edge u w).neighborFinset w = {u} := by
    ext y
    simp only [mem_neighborFinset, edge_adj, Finset.mem_singleton]
    aesop
  by_cases hxu : x = u
  · subst x
    simp [degree, hnu]
  · by_cases hxw : x = w
    · subst x
      simp [degree, hnw]
    · have hn : (edge u w).neighborFinset x = ∅ := by
        ext y
        simp [mem_neighborFinset, edge_adj, hxu, hxw]
      simp [degree, hn, hxu, hxw]

theorem degree_sup_edge (G : SimpleGraph V) (u w x : V)
    (huw : u ≠ w) (hguw : ¬G.Adj u w) :
    (G ⊔ edge u w).degree x = G.degree x + if x = u ∨ x = w then 1 else 0 := by
  have hd : Disjoint G (edge u w) := (disjoint_edge G).mpr hguw
  unfold degree
  rw [neighborFinset_sup_of_disjoint x hd, Finset.card_disjUnion]
  exact congrArg (fun k : ℕ => (G.neighborFinset x).card + k) (degree_edge u w x huw)

/-- The number of degree-one vertices, including all vertex labels. -/
def leafCount (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun x => G.degree x = 1).card

theorem leaf_count_iso {W : Type*} [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) :
    leafCount G = leafCount H := by
  unfold leafCount
  apply Finset.card_bij (fun x _ => f x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f.degree_eq] using hx
  · intro x _ y _ hxy
    exact f.injective hxy
  · intro y hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f.symm.degree_eq] using hy

/-- Exactly the old endpoint ceases to be a leaf; every other leaf is retained.
The base root has degree at least two, and the first-arm endpoint has degree one. -/
theorem leaf_count_rewire (G : SimpleGraph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w)
    (hdu : 2 ≤ G.degree u) (hdv : G.degree v = 1) :
    leafCount (G ⊔ edge u w) = leafCount (G ⊔ edge v w) + 1 := by
  have hv : v ∉ Finset.univ.filter (fun x => (G ⊔ edge v w).degree x = 1) := by
    simp [degree_sup_edge G v w v hvw hgvw, hdv]
  have he : Finset.univ.filter (fun x => (G ⊔ edge u w).degree x = 1) =
      insert v (Finset.univ.filter fun x => (G ⊔ edge v w).degree x = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      degree_sup_edge G u w x huw hguw, degree_sup_edge G v w x hvw hgvw]
    by_cases hxu : x = u
    · subst x
      simp [huv, huw]
      omega
    · by_cases hxv : x = v
      · subst x
        simp [Ne.symm huv, hvw, hdv]
      · by_cases hxw : x = w <;> simp_all
  simpa only [leafCount, Finset.card_insert_of_notMem hv] using congrArg Finset.card he

/-- A natural-number descent measure for every genuine pendant-path fusion. -/
theorem leaf_count_strict (G : SimpleGraph V) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w)
    (hdu : 2 ≤ G.degree u) (hdv : G.degree v = 1) :
    leafCount (G ⊔ edge v w) < leafCount (G ⊔ edge u w) := by
  rw [leaf_count_rewire G u v w huv huw hvw hguw hgvw hdu hdv]
  omega

#print axioms reachable_transfer
#print axioms connected_rewire
#print axioms edge_count_rewire
#print axioms tree_rewire
#print axioms degree_sup_edge
#print axioms leaf_count_iso
#print axioms leaf_count_rewire
#print axioms leaf_count_strict

end
end Gebendorfer.RadenkovicGutman.RewireTopology
