import Proofs.PendantSupport

/-! The two neighborhood bounds in Gebendorfer's WOWII 412e manuscript.
The original conventions and the empty induced graph are retained. -/
namespace WOWII412eBounds
open Finset SimpleGraph WOWII412dCore CoronaExchange PendantSupport
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def maxDegreeOn (A : Finset V) : ℕ := by
  classical
  exact (G.induce (A : Set V)).maxDegree

omit [Fintype V] [DecidableEq V] in
lemma common_neighbor_not_adj (hb : G.IsBipartite) {v u w : V}
    (hvu : G.Adj v u) (hvw : G.Adj v w) : ¬ G.Adj u w := by
  obtain ⟨c, hc⟩ := hb
  intro huw
  have h1 : c v ≠ c u := hc hvu
  have h2 : c v ≠ c w := hc hvw
  have h3 : c u ≠ c w := hc huw
  have hu := (c u).isLt
  have hw := (c w).isLt
  have hv := (c v).isLt
  omega

omit [DecidableEq V] in
lemma neighbor_independent [DecidableRel G.Adj] (hb : G.IsBipartite) (v : V) :
    Independent G (G.neighborFinset v) := by
  intro u hu w hw huw
  exact common_neighbor_not_adj G hb (by simpa using hu) (by simpa using hw) huw

/-- A vertex in the twice-literal neighborhood has a pendant outside its
induced neighborhood. Otherwise all supports would be that vertex itself. -/
lemma leaf_outside_induced_neighbors [DecidableRel G.Adj]
    (v : V) (hv : v ∈ neighbors G (supports G)) :
    ∃ p ∈ leaves G, p ∉ G.neighborFinset v ∩ neighbors G (supports G) := by
  classical
  by_contra! hn
  have hS : ∀ s ∈ supports G, s = v := by
    intro s hs
    obtain ⟨p, hp, hps⟩ : ∃ p ∈ leaves G, G.Adj p s := by
      simpa only [supports, neighbors, mem_filter, mem_univ, true_and] using hs
    have hpv : G.Adj p v := by
      have ht := (mem_inter.mp (hn p hp)).1
      exact ((G.mem_neighborFinset v p).mp ht).symm
    obtain ⟨a, _ha, huniq⟩ := leaf_unique_neighbor G hp
    exact (huniq s hps).trans (huniq v hpv).symm
  obtain ⟨s, hs, hsv⟩ : ∃ s ∈ supports G, G.Adj s v := by
    simpa only [neighbors, mem_filter, mem_univ, true_and] using hv
  exact hsv.ne (hS s hs)

/-- The literal-neighborhood inequality. -/
theorem literal_bound (hb : G.IsBipartite) (horder : 2 < Fintype.card V) :
    1 + maxDegreeOn G (neighbors G (supports G)) ≤ (corona G).card := by
  classical
  let Q := neighbors G (supports G)
  have htwo := (bipartite_indepNum_ge_two G hb horder).trans (indepNum_le_corona G)
  have hm : maxDegreeOn G Q ≤ (corona G).card - 1 := by
    unfold maxDegreeOn
    apply maxDegree_le_of_forall_degree_le
    intro v
    let T := G.neighborFinset v.val ∩ Q
    have hT : Independent G T := fun u hu w hw =>
      neighbor_independent G hb v.val u (mem_inter.mp hu).1 w (mem_inter.mp hw).1
    obtain ⟨p, hp, hpT⟩ := leaf_outside_induced_neighbors G v.val v.property
    have hL : ({p} : Finset V) ⊆ corona G := by
      simpa only [singleton_subset_iff] using leaves_subset_corona G hp
    have hDL : Disjoint T {p} := by
      rw [Finset.disjoint_singleton_right]
      exact hpT
    have hc := reserved_cardinality G T {p} hT hL hDL (Or.inl (by simp))
    have he := induced_degree_eq G Q v
    change (G.induce (Q : Set V)).degree v = T.card at he
    simp only [card_singleton] at hc
    omega
  change 1 + maxDegreeOn G Q ≤ _
  omega

omit [DecidableEq V] in
/-- With at most one pendant, all vertices in the twice-literal neighborhood
share a support, so that neighborhood is independent in a bipartite graph. -/
lemma second_neighbors_independent [DecidableRel G.Adj] (hb : G.IsBipartite)
    (hsmall : (leaves G).card ≤ 1) : Independent G (neighbors G (supports G)) := by
  classical
  intro u hu w hw huw
  obtain ⟨s, hs, hsu⟩ : ∃ s ∈ supports G, G.Adj s u := by
    simpa only [neighbors, mem_filter, mem_univ, true_and] using hu
  obtain ⟨t, ht, htw⟩ : ∃ t ∈ supports G, G.Adj t w := by
    simpa only [neighbors, mem_filter, mem_univ, true_and] using hw
  obtain ⟨p, hp, hps⟩ : ∃ p ∈ leaves G, G.Adj p s := by
    simpa only [supports, neighbors, mem_filter, mem_univ, true_and] using hs
  obtain ⟨q, hq, hqt⟩ : ∃ q ∈ leaves G, G.Adj q t := by
    simpa only [supports, neighbors, mem_filter, mem_univ, true_and] using ht
  have hpq : p = q := card_le_one.mp hsmall p hp q hq
  subst q
  obtain ⟨a, _ha, huniq⟩ := leaf_unique_neighbor G hp
  have hst : s = t := (huniq s hps).trans (huniq t hqt).symm
  subst t
  exact common_neighbor_not_adj G hb hsu htw huw

/-- The sharper external-neighborhood independence bound. -/
theorem external_bound (hG : G.Connected) (hb : G.IsBipartite)
    (horder : 2 < Fintype.card V) :
    maxDegreeOn G (neighbors G (supports G) \ supports G) + max 2 (leaves G).card ≤
      G.indepNum := by
  classical
  let Q := neighbors G (supports G) \ supports G
  have hP := leaves_independent G hG horder
  have htwo := bipartite_indepNum_ge_two G hb horder
  by_cases hsmall : (leaves G).card ≤ 1
  · have hi := second_neighbors_independent G hb hsmall
    have hz : maxDegreeOn G Q = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold maxDegreeOn
      apply maxDegree_le_of_forall_degree_le
      intro v
      rw [induced_degree_eq G Q v]
      apply Nat.le_zero.mpr
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hi v.val (mem_sdiff.mp v.property).1 w (mem_sdiff.mp (mem_inter.mp hw).2).1
        (by simpa using (mem_inter.mp hw).1)
    change maxDegreeOn G Q + max 2 (leaves G).card ≤ _
    rw [hz, zero_add, max_eq_left (by omega)]
    exact htwo
  · have hlarge : 2 ≤ (leaves G).card := by omega
    have hm : maxDegreeOn G Q ≤ G.indepNum - (leaves G).card := by
      unfold maxDegreeOn
      apply maxDegree_le_of_forall_degree_le
      intro v
      let T := G.neighborFinset v.val ∩ Q
      have hT : Independent G T := fun u hu w hw =>
        neighbor_independent G hb v.val u (mem_inter.mp hu).1 w (mem_inter.mp hw).1
      have hcross : ∀ p ∈ leaves G, ∀ w ∈ T, ¬ G.Adj p w := by
        intro p hp w hw hpw
        exact (mem_sdiff.mp (mem_inter.mp hw).2).2 (support_of_adj_leaf G hp hpw)
      have hd : Disjoint (leaves G) T := by
        rw [Finset.disjoint_left]
        intro p hp ht
        have hvp : G.Adj p v.val := ((G.mem_neighborFinset v.val p).mp (mem_inter.mp ht).1).symm
        exact (mem_sdiff.mp v.property).2 (support_of_adj_leaf G hp hvp)
      have hi : Independent G (leaves G ∪ T) := by
        intro a ha b hb hab
        rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
        · exact hP a ha b hb hab
        · exact hcross a ha b hb hab
        · exact hcross b hb a ha hab.symm
        · exact hT a ha b hb hab
      have hc := independent_card_le_indepNum G _ hi
      rw [card_union_of_disjoint hd] at hc
      have he := induced_degree_eq G Q v
      change (G.induce (Q : Set V)).degree v = T.card at he
      omega
    have hp := independent_card_le_indepNum G (leaves G) hP
    change maxDegreeOn G Q + max 2 (leaves G).card ≤ _
    rw [max_eq_right hlarge]
    omega

end WOWII412eBounds
