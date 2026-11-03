/-
Copyright (c) 2026 Jonas J. Gebendorfer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas J. Gebendorfer
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Tactic
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SpanningTree

/-!
# A complete proof of Written on the Wall II, Conjecture 161

The argument follows Gebendorfer, *Proper cliques and spanning-tree leaves*
(28 October 2026), DOI 10.13140/RG.2.2.31746.44485.
The spanning-subgraph conversion and supremum bound follow the corresponding
helpers in MiskinAleksandr23/WOWII-1, commit
eda16f6e96b313bd112351ae9859133b77d537c9, under the Apache 2.0 license.
-/

@[expose] public section

namespace WOWII161

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The handshaking identity bounds every tree degree by its number of leaves. -/
lemma tree_degree_le_leaves (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (v : V) :
    T.degree v ≤ (univ.filter fun w => T.degree w = 1).card := by
  classical
  rcases subsingleton_or_nontrivial V with h | h
  · let _ := h
    simp
  · let _ := h
    let f : V → ℕ := fun w => T.degree w + if T.degree w = 1 then 1 else 0
    have hf (w : V) : 2 ≤ f w := by
      have hp := hT.connected.preconnected.degree_pos_of_nontrivial w
      dsimp [f]
      split_ifs <;> omega
    have hs := sum_le_sum (s := univ.erase v) (fun w _ => hf w)
    have hc : (univ.erase v : Finset V).card + 1 = Fintype.card V := by
      simpa using card_erase_add_one (mem_univ v)
    have hsum : (∑ w ∈ univ.erase v, f w) + f v =
        2 * T.edgeFinset.card + (univ.filter fun w => T.degree w = 1).card := by
      rw [sum_erase_add _ _ (mem_univ v)]
      simp only [f, sum_add_distrib]
      rw [T.sum_degrees_eq_twice_card_edges]
      simp
    have he := hT.card_edgeFinset
    simp only [sum_const, smul_eq_mul] at hs
    have hv : T.degree v ≤ f v := Nat.le_add_right _ _
    omega

open scoped Classical in
/-- A concrete spanning tree contributes its leaf count to the defining supremum. -/
lemma leaf_card_le_Ls (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Subgraph G) (hTsp : T.IsSpanning) (hTtree : IsTree T.coe) :
    ((T.verts.toFinset.filter fun v => T.degree v = 1).card : ℝ) ≤ Ls G := by
  classical
  unfold Ls
  apply le_csSup
  · refine ⟨(Fintype.card V : ℝ), ?_⟩
    rintro x ⟨S, _hS, rfl⟩
    change ((S.verts.toFinset.filter fun v => S.degree v = 1).card : ℝ) ≤ _
    exact_mod_cast (le_trans (Finset.card_filter_le _ _) S.verts.toFinset.card_le_univ)
  · exact ⟨T, ⟨hTsp, hTtree⟩, rfl⟩

/-- Keeping the entire star at a vertex gives a spanning tree with at least its degree
many leaves. This also covers the one-vertex graph, whose degree is zero. -/
lemma degree_le_Ls (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (v : V) : (G.degree v : ℝ) ≤ Ls G := by
  classical
  let H := G ⊓ starGraph v
  have hH : H.IsAcyclic := (isAcyclic_starGraph v).anti inf_le_right
  obtain ⟨T, hHT, hTG, hT⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic (show H ≤ G from inf_le_left) hH
  have hn : H.neighborFinset v = G.neighborFinset v := by
    ext w
    simp only [mem_neighborFinset, H, inf_adj, starGraph_adj]
    exact ⟨fun h => h.1, fun h => ⟨h, h.ne, Or.inl trivial⟩⟩
  have hd : G.degree v ≤ T.degree v := by
    have hh : H.degree v = G.degree v := by
      simpa only [card_neighborFinset_eq_degree] using congrArg Finset.card hn
    exact hh ▸ degree_le_of_le hHT
  let S := G.toSubgraph T hTG
  have hSsp : S.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  have hStree : IsTree S.coe := by
    apply (S.spanningCoeEquivCoeOfSpanning hSsp).isTree_iff.mp
    exact hT
  have hleaves : S.verts.toFinset.filter (fun w => S.degree w = 1) =
      univ.filter (fun w => T.degree w = 1) := by
    ext w
    simp [S]
  have hb := leaf_card_le_Ls G S hSsp hStree
  rw [hleaves] at hb
  calc
    (G.degree v : ℝ) ≤ ((univ.filter fun w => T.degree w = 1).card : ℝ) := by
      exact_mod_cast hd.trans (tree_degree_le_leaves T hT v)
    _ ≤ Ls G := hb

/-- A walk from a set to its complement contains an edge crossing its boundary. -/
lemma crossing_edge (G : SimpleGraph V) (s : Finset V) {a b : V}
    (p : G.Walk a b) (ha : a ∈ s) (hb : b ∉ s) :
    ∃ x ∈ s, ∃ y ∉ s, G.Adj x y := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b hac p ih =>
    by_cases hc : c ∈ s
    · exact ih hc hb
    · exact ⟨a, ha, c, hc, hac⟩

/-- Every proper clique is bounded by the leaf number of a connected graph. -/
lemma proper_clique_card_le_Ls (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (s : Finset V) (hs : G.IsClique (s : Set V))
    (b : V) (hb : b ∉ s) : (s.card : ℝ) ≤ Ls G := by
  classical
  by_cases hn : s.Nonempty
  · obtain ⟨a, ha⟩ := hn
    obtain ⟨p⟩ := hG.preconnected a b
    obtain ⟨x, hx, y, hy, hxy⟩ := crossing_edge G s p ha hb
    have hsub : insert y (s.erase x) ⊆ G.neighborFinset x := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact (G.mem_neighborFinset x z).mpr hxy
      · exact (G.mem_neighborFinset x z).mpr (hs hx (mem_of_mem_erase hz)
          (ne_of_mem_erase hz).symm)
    have hy' : y ∉ s.erase x := fun h => hy (mem_of_mem_erase h)
    have hcard : (insert y (s.erase x)).card = s.card := by
      rw [card_insert_of_notMem hy']
      exact card_erase_add_one hx
    have hdeg : s.card ≤ G.degree x := by
      simpa only [hcard, card_neighborFinset_eq_degree] using card_le_card hsub
    calc
      (s.card : ℝ) ≤ (G.degree x : ℝ) := by exact_mod_cast hdeg
      _ ≤ Ls G := degree_le_Ls G hG x
  · have hzero : s = ∅ := not_nonempty_iff_eq_empty.mp hn
    subst s
    have := degree_le_Ls G hG b
    simpa using (by positivity : (0 : ℝ) ≤ (G.degree b : ℝ)).trans this

/-- An independent set in a complement neighbourhood is a proper clique. -/
lemma local_complement_le_Ls (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (v : V) :
    (((Gᶜ.induce (Gᶜ.neighborSet v)).indepNum : ℕ) : ℝ) ≤ Ls G := by
  classical
  let H := Gᶜ.induce (Gᶜ.neighborSet v)
  obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
  let S : Finset V := s.map ⟨Subtype.val, Subtype.val_injective⟩
  have hS : G.IsClique (S : Set V) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
    have hab : a ≠ b := fun h => hxy (congrArg Subtype.val h)
    have hi := hs.isIndepSet ha hb hab
    change ¬ (a.val ≠ b.val ∧ ¬ G.Adj a.val b.val) at hi
    exact not_not.mp (fun h => hi ⟨hxy, h⟩)
  have hv : v ∉ S := by
    intro hv
    obtain ⟨a, _, hav⟩ := mem_map.mp hv
    exact a.property.1 hav.symm
  have hcard : S.card = H.indepNum := by
    simpa [S] using hs.card_eq
  have hb := proper_clique_card_le_Ls G hG S hS v hv
  rw [hcard] at hb
  exact hb

end WOWII161

namespace WrittenOnTheWallII.GraphConjecture161

open SimpleGraph Finset

/-- For every finite connected simple graph, the maximum local independence number
of its complement is at most the maximum number of leaves in a spanning tree. -/
theorem conjecture161_proved {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (h_conn : G.Connected) :
    (maxLocalIndependence Gᶜ : ℝ) ≤ Ls G := by
  classical
  let _ : Nonempty α := h_conn.nonempty
  let f : α → ℕ := fun v => (Gᶜ.induce (Gᶜ.neighborSet v)).indepNum
  obtain ⟨n, hn, hmax⟩ := mem_image.mp
    (max_mem_image_coe (univ_nonempty.image f))
  obtain ⟨v, _, rfl⟩ := mem_image.mp hn
  have hm : maxLocalIndependence Gᶜ = f v := by
    change (univ.image f).max.getD 0 = f v
    rw [← hmax]
    rfl
  rw [hm]
  exact WOWII161.local_complement_le_Ls G h_conn v

end WrittenOnTheWallII.GraphConjecture161
