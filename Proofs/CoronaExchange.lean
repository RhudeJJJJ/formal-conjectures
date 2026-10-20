import Proofs.WOWII412dCore
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Independent-set exchange and reserved corona vertices

Source: Gebendorfer, Pendant-Support Inequalities for Graph Coronas,
1 September 2026, and A neighborhood-exchange bound, 1 September 2026.
The reserved-cardinality argument applies strict Hall only to the entire
independent set outside the corona; no matching theorem is needed for it.
-/
namespace CoronaExchange
open Finset SimpleGraph WOWII412dCore
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma independent_card_le_corona (D : Finset V) (hD : Independent G D) :
    D.card ≤ (corona G).card := by
  obtain ⟨M, hM⟩ := exists_maximum G
  exact (hM.2 D hD).trans (card_le_card (maximum_subset_corona G M hM))

omit [Fintype V] [DecidableEq V] in
lemma maximum_of_card (M D : Finset V) (hM : Maximum G M)
    (hD : Independent G D) (hc : M.card ≤ D.card) : Maximum G D :=
  ⟨hD, fun J hJ => (hM.2 J hJ).trans hc⟩

omit [Fintype V] in
lemma swap_maximum (M : Finset V) (hM : Maximum G M) {v s : V}
    (hv : v ∉ M) (hs : s ∈ M) (huniq : ∀ w ∈ M, G.Adj v w → w = s) :
    Maximum G (insert v (M.erase s)) := by
  have hi : Independent G (insert v (M.erase s)) := by
    intro a ha b hb hab
    by_cases hav : a = v
    · subst a
      by_cases hbv : b = v
      · subst b
        exact hab.ne rfl
      · have hbE := (mem_insert.mp hb).resolve_left hbv
        exact (mem_erase.mp hbE).1 (huniq b (mem_erase.mp hbE).2 hab)
    · have haE := (mem_insert.mp ha).resolve_left hav
      by_cases hbv : b = v
      · subst b
        exact (mem_erase.mp haE).1 (huniq a (mem_erase.mp haE).2 hab.symm)
      · exact hM.1 a (mem_erase.mp haE).2 b
          (mem_erase.mp ((mem_insert.mp hb).resolve_left hbv)).2 hab
  have hc : (insert v (M.erase s)).card = M.card := by
    rw [card_insert_of_notMem (fun h => hv (mem_of_mem_erase h)), card_erase_of_mem hs]
    have := card_pos.mpr ⟨s, hs⟩
    omega
  exact maximum_of_card G M _ hM hi hc.symm.le

lemma leaf_mem_corona [DecidableRel G.Adj] {p : V} (hp : G.degree p = 1) :
    p ∈ corona G := by
  classical
  obtain ⟨M, hM⟩ := exists_maximum G
  by_cases hpm : p ∈ M
  · exact maximum_subset_corona G M hM hpm
  · have hpn : p ∈ neighbors G M := by rw [maximum_neighbors G M hM]; simp [hpm]
    obtain ⟨s, hs, hsp⟩ : ∃ s ∈ M, G.Adj s p := by
      simpa only [neighbors, mem_filter, mem_univ, true_and] using hpn
    obtain ⟨a, _ha, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hp
    have hswap := swap_maximum G M hM hpm hs
      (fun w _ hw => (huniq w hw).trans (huniq s hsp.symm).symm)
    exact maximum_subset_corona G _ hswap (mem_insert_self _ _)

/-- Strict Hall for one independent subset outside the corona in any graph. -/
lemma strict_neighbors (M X : Finset V) (hM : Maximum G M)
    (hX : Independent G X) (hXC : Disjoint X (corona G)) (hne : X.Nonempty) :
    X.card + 1 ≤ (neighbors G X ∩ M).card := by
  classical
  let B := neighbors G X ∩ M
  let J := (M \ B) ∪ X
  have hXM : Disjoint X M := hXC.mono_right (maximum_subset_corona G M hM)
  have hi : Independent G J := by
    intro a ha b hb hab
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact hM.1 a (mem_sdiff.mp ha).1 b (mem_sdiff.mp hb).1 hab
    · exact (mem_sdiff.mp ha).2 (mem_inter.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, b, hb, hab.symm⟩, (mem_sdiff.mp ha).1⟩)
    · exact (mem_sdiff.mp hb).2 (mem_inter.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, a, ha, hab⟩, (mem_sdiff.mp hb).1⟩)
    · exact hX a ha b hb hab
  have hd : Disjoint (M \ B) X := hXM.symm.mono_left sdiff_subset
  have hc : J.card = (M \ B).card + X.card := card_union_of_disjoint hd
  have hbm : B ⊆ M := inter_subset_right
  have hbc := card_sdiff_add_card_eq_card hbm
  by_contra hn
  change ¬ X.card + 1 ≤ B.card at hn
  have hle : M.card ≤ J.card := by omega
  have hj := maximum_of_card G M J hM hi hle
  obtain ⟨x, hx⟩ := hne
  exact Finset.disjoint_left.mp hXC hx
    (maximum_subset_corona G J hj (mem_union_right _ hx))

/-- Reserve either at most one corona vertex or a corona set with no edges
into the independent set outside the corona. Only cardinality is asserted. -/
lemma reserved_cardinality (D L : Finset V) (hD : Independent G D)
    (hL : L ⊆ corona G) (hDL : Disjoint D L)
    (hcase : L.card ≤ 1 ∨ ∀ x ∈ D \ corona G, ∀ y ∈ L, ¬ G.Adj x y) :
    D.card + L.card ≤ (corona G).card := by
  classical
  let X := D \ corona G
  let D₁ := D ∩ corona G
  have hXD : X ⊆ D := sdiff_subset
  have hX : Independent G X := fun u hu v hv => hD u (hXD hu) v (hXD hv)
  have hXC : Disjoint X (corona G) := sdiff_disjoint
  have hD₁ : D₁ ⊆ corona G := inter_subset_right
  have hsplit : X.card + D₁.card = D.card := card_sdiff_add_card_inter D (corona G)
  have hD₁L : Disjoint D₁ L := hDL.mono_left inter_subset_left
  by_cases hne : X.Nonempty
  · obtain ⟨M, hM⟩ := exists_maximum G
    let B := neighbors G X ∩ M
    have hB := strict_neighbors G M X hM hX hXC hne
    have hBC : B ⊆ corona G := inter_subset_right.trans (maximum_subset_corona G M hM)
    have hBD : Disjoint B D₁ := by
      rw [Finset.disjoint_left]
      intro v hv hd
      obtain ⟨x, hx, hxv⟩ := (mem_filter.mp (mem_inter.mp hv).1).2
      exact hD x (hXD hx) v (mem_inter.mp hd).1 hxv
    rcases hcase with hsmall | hnoedge
    · have hsub : B ∪ D₁ ⊆ corona G := union_subset hBC hD₁
      have hc := card_le_card hsub
      rw [card_union_of_disjoint hBD] at hc
      change X.card + 1 ≤ B.card at hB
      omega
    · have hBL : Disjoint B L := by
        rw [Finset.disjoint_left]
        intro v hv hl
        obtain ⟨x, hx, hxv⟩ := (mem_filter.mp (mem_inter.mp hv).1).2
        exact hnoedge x hx v hl hxv
      have hsub : (B ∪ D₁) ∪ L ⊆ corona G := union_subset (union_subset hBC hD₁) hL
      have hc := card_le_card hsub
      rw [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hBL, hD₁L⟩), card_union_of_disjoint hBD] at hc
      change X.card + 1 ≤ B.card at hB
      omega
  · have he : X = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hc := card_le_card (union_subset hD₁ hL)
    rw [card_union_of_disjoint hD₁L] at hc
    simp only [he, card_empty, zero_add] at hsplit
    omega

end CoronaExchange
