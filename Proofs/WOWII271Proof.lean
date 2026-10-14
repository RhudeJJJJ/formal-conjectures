/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

/-!
# Total domination and distance between maximum-degree vertices

Author: Jonas J. Gebendorfer. Formalization assisted by OpenAI Codex.
Written source: *Total domination and distance between maximum-degree vertices*,
12 October 2026. The component-sensitive classical diameter estimate is credited
to DeLaVina, Liu, Pepper, Waller and West (2007), Lemma 3.
-/

open SimpleGraph Finset
namespace WOWII271Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_le_span (S : Finset ℕ) (k : ℕ)
    (hspan : ∀ i ∈ S, ∀ j ∈ S, i ≤ j + k) : S.card ≤ k + 1 := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha, hmin⟩ := S.exists_min_image id hne
    have hsub : S ⊆ Finset.Icc a (a + k) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨hmin j hj, hspan j hj a ha⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at this
    omega
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [this]

omit [Fintype V] [DecidableEq V] in
/-- A shortest walk has its expected distance from the initial vertex at every index. -/
lemma prefix_distance {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i : ℕ} (hi : i ≤ p.length) :
    G.dist u (p.getVert i) = i := by
  have h := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  rw [p.take_length, Nat.min_eq_left hi] at h
  exact h.symm

omit [DecidableEq V] in
/-- The vertex counts of connected components sum to the total vertex count. -/
lemma sum_component_card (H : SimpleGraph V)
    [Fintype H.ConnectedComponent] [∀ C : H.ConnectedComponent, Fintype C] :
    ∑ C : H.ConnectedComponent, Fintype.card C = Fintype.card V := by
  classical
  let e : (Σ C : H.ConnectedComponent, C) ≃ V :=
    { toFun := fun x => x.2.val
      invFun := fun x => ⟨H.connectedComponentMk x, ⟨x, rfl⟩⟩
      left_inv := by
        rintro ⟨C, x, hx⟩
        change H.connectedComponentMk x = C at hx
        cases hx
        rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr e

omit [Fintype V] in
/-- Each component of the selected induced graph contains two distinct vertices. -/
lemma component_card_ge_two (G : SimpleGraph V) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V))
    (C : (G.induce (D : Set V)).ConnectedComponent) [Fintype C] :
    2 ≤ Fintype.card C := by
  classical
  obtain ⟨x, hx⟩ := C.nonempty_supp
  obtain ⟨y, hyD, hxy⟩ := hD x.val
  let y' : {v // v ∈ (D : Set V)} := ⟨y, hyD⟩
  have hy : y' ∈ C := C.mem_supp_of_adj_mem_supp hx hxy
  have hne : (⟨x, hx⟩ : C) ≠ ⟨y', hy⟩ := by
    intro h
    exact hxy.ne (congrArg (fun z : C => z.val.val) h)
  have hcard := Finset.card_le_univ ({⟨x, hx⟩, ⟨y', hy⟩} : Finset C)
  simpa [hne] using hcard

omit [Fintype V] [DecidableEq V] in
/-- The indices of a geodesic reached from one selected component have bounded span. -/
lemma component_reaches_span (G : SimpleGraph V) (hG : G.Connected) (D : Finset V)
    (C : (G.induce (D : Set V)).ConnectedComponent) [Fintype C]
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length)
    (yi yj : C) (hiy : G.Adj (p.getVert i) yi.val.val)
    (hjy : G.Adj (p.getVert j) yj.val.val) :
    i ≤ j + Fintype.card C + 1 := by
  obtain ⟨q, hq, _⟩ := C.connected_toSimpleGraph.exists_path_of_dist yj yi
  let f : C.toSimpleGraph →g G :=
    (SimpleGraph.Embedding.induce (D : Set V)).toHom.comp C.toSimpleGraph_hom
  have hwalk : G.dist yj.val.val yi.val.val ≤ q.length := by
    have hm := SimpleGraph.dist_le (q.map f)
    rw [SimpleGraph.Walk.length_map] at hm
    exact hm
  have hlen := hq.length_lt
  have h₁ := hG.dist_triangle (u := p.getVert j) (v := yj.val.val) (w := yi.val.val)
  have h₂ := hG.dist_triangle (u := p.getVert j) (v := yi.val.val) (w := p.getVert i)
  have h₃ := hG.dist_triangle (u := u) (v := p.getVert j) (w := p.getVert i)
  rw [prefix_distance p hp hi, prefix_distance p hp hj] at h₃
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hjy] at h₁
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hiy.symm] at h₂
  omega

omit [DecidableEq V] in
/-- Component-sensitive diameter estimate, stated for every pair of endpoints. -/
theorem component_distance_bound (G : SimpleGraph V) (hG : G.Connected)
    (D : Finset V) (hD : G.IsTotalDominating (D : Set V)) (u v : V)
    [Fintype (G.induce (D : Set V)).ConnectedComponent] :
    G.dist u v + 1 ≤ D.card + 2 * Fintype.card (G.induce (D : Set V)).ConnectedComponent := by
  classical
  let H := G.induce (D : Set V)
  let (C : H.ConnectedComponent) : Fintype C := Fintype.ofFinite C
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist u v
  let reached (C : H.ConnectedComponent) : Finset ℕ :=
    (Finset.range (p.length + 1)).filter fun i => ∃ y : C, G.Adj (p.getVert i) y.val.val
  have hcover : Finset.range (p.length + 1) ⊆ Finset.univ.biUnion reached := by
    intro i hi
    obtain ⟨y, hyD, hiy⟩ := hD (p.getVert i)
    let y' : {v // v ∈ (D : Set V)} := ⟨y, hyD⟩
    exact Finset.mem_biUnion.mpr ⟨H.connectedComponentMk y', Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hi, ⟨⟨y', rfl⟩, hiy⟩⟩⟩
  have hreach (C : H.ConnectedComponent) : (reached C).card ≤ Fintype.card C + 2 := by
    apply (card_le_span (reached C) (Fintype.card C + 1) ?_).trans_eq
    · omega
    · intro i hi j hj
      obtain ⟨hi, yi, hiy⟩ := Finset.mem_filter.mp hi
      obtain ⟨hj, yj, hjy⟩ := Finset.mem_filter.mp hj
      have h := component_reaches_span G hG D C p hp
        (by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi)
        (by simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj) yi yj hiy hjy
      omega
  have hsum := sum_component_card H
  have hsum' : (∑ C : H.ConnectedComponent, Fintype.card C) = D.card := by
    exact hsum.trans (Fintype.card_of_finset' D (fun _ => Iff.rfl))
  calc
    G.dist u v + 1 = (Finset.range (p.length + 1)).card := by simp [hp]
    _ ≤ (Finset.univ.biUnion reached).card := Finset.card_le_card hcover
    _ ≤ ∑ C : H.ConnectedComponent, (reached C).card := Finset.card_biUnion_le
    _ ≤ ∑ C : H.ConnectedComponent, (Fintype.card C + 2) := Finset.sum_le_sum (fun C _ => hreach C)
    _ = D.card + 2 * Fintype.card H.ConnectedComponent := by
      rw [Finset.sum_add_distrib, hsum']
      simp [Nat.mul_comm]

/-- Total domination prevents singleton selected components. -/
lemma twice_component_count_le (G : SimpleGraph V) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V))
    [Fintype (G.induce (D : Set V)).ConnectedComponent] :
    2 * Fintype.card (G.induce (D : Set V)).ConnectedComponent ≤ D.card := by
  classical
  let H := G.induce (D : Set V)
  let (C : H.ConnectedComponent) : Fintype C := Fintype.ofFinite C
  have hsum := sum_component_card H
  have hc := Finset.sum_le_sum (s := (Finset.univ : Finset H.ConnectedComponent))
    (fun C _ => component_card_ge_two G D hD C)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hc
  rw [hsum, Fintype.card_of_finset' D (fun _ => Iff.rfl)] at hc
  simpa only [Nat.mul_comm] using hc

theorem total_domination_distance_bound (G : SimpleGraph V) (hG : G.Connected)
    (D : Finset V) (hD : G.IsTotalDominating (D : Set V)) (u v : V) :
    G.dist u v + 1 ≤ 2 * D.card := by
  classical
  let : Fintype (G.induce (D : Set V)).ConnectedComponent := Fintype.ofFinite _
  have h₁ := component_distance_bound G hG D hD u v
  have h₂ := twice_component_count_le G D hD
  omega

omit [Fintype V] in
/-- A total dominating set in a nonempty simple graph has at least two vertices. -/
lemma total_set_card_ge_two (G : SimpleGraph V) [Nonempty V] (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) : 2 ≤ D.card := by
  classical
  obtain ⟨a, ha, _⟩ := hD (Classical.choice (inferInstance : Nonempty V))
  obtain ⟨b, hb, hab⟩ := hD a
  have hsub : ({a, b} : Finset V) ⊆ D := by
    exact Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
  have hc := Finset.card_le_card hsub
  simpa [hab.ne] using hc

/-- The maximum-degree endpoints of a graph with a two-element total dominating set
are at distance at most two. This uses open-neighborhood counting, not the diameter bound. -/
lemma maximum_degree_distance_of_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 2)
    (u v : V) (hu : G.degree u = G.maxDegree) (hv : G.degree v = G.maxDegree) :
    G.dist u v ≤ 2 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hcover : Finset.univ ⊆ G.neighborFinset a ∪ G.neighborFinset b := by
    intro x _
    obtain ⟨y, hy, hxy⟩ := hD x
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_union_left _ (by simpa using hxy.symm)
    · have : y = b := Finset.mem_singleton.mp hy
      subst y
      exact Finset.mem_union_right _ (by simpa using hxy.symm)
  have hupper : Fintype.card V ≤ 2 * G.maxDegree := by
    have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    simp only [Finset.card_univ, SimpleGraph.card_neighborFinset_eq_degree] at hc
    have ha := G.degree_le_maxDegree a
    have hb := G.degree_le_maxDegree b
    omega
  by_contra hn
  have hdist : 2 < G.dist u v := by omega
  have huv : u ≠ v := by intro h; subst v; simp at hdist
  have hnadj : ¬G.Adj u v := by
    intro h
    have := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  have hdis : Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
    apply Finset.disjoint_left.mpr
    intro x hxu hxv
    have hux : G.Adj u x := by simpa using hxu
    have hvx : G.Adj v x := by simpa using hxv
    have hwalk := SimpleGraph.dist_le (SimpleGraph.Walk.cons hux
      (SimpleGraph.Walk.cons hvx.symm SimpleGraph.Walk.nil))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hwalk
    omega
  have huout : u ∉ G.neighborFinset u ∪ G.neighborFinset v := by
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨G.irrefl, fun h => hnadj h.symm⟩
  have hvout : v ∉ G.neighborFinset u ∪ G.neighborFinset v := by
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, not_or]
    exact ⟨hnadj, G.irrefl⟩
  have hc := Finset.card_le_univ
    (insert u (insert v (G.neighborFinset u ∪ G.neighborFinset v)))
  rw [Finset.card_insert_of_notMem (by simp [huv, huout]),
    Finset.card_insert_of_notMem hvout, Finset.card_union_of_disjoint hdis] at hc
  simp only [SimpleGraph.card_neighborFinset_eq_degree, hu, hv] at hc
  omega

/-- Every total dominating set satisfies the squared WOWII271 inequality. -/
theorem squared_bound_for_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (u v : V) (hu : G.degree u = G.maxDegree) (hv : G.degree v = G.maxDegree) :
    2 * G.dist u v ≤ D.card ^ 2 := by
  classical
  have : Nonempty V := ⟨u⟩
  have htwo := total_set_card_ge_two G D hD
  by_cases h₂ : D.card = 2
  · have := maximum_degree_distance_of_pair G D hD h₂ u v hu hv
    nlinarith
  · by_cases h₃ : D.card = 3
    · let : Fintype (G.induce (D : Set V)).ConnectedComponent := Fintype.ofFinite _
      have hc := twice_component_count_le G D hD
      have hd := component_distance_bound G hG D hD u v
      have hc' : Fintype.card (G.induce (D : Set V)).ConnectedComponent ≤ 1 := by omega
      nlinarith
    · have hlarge : 4 ≤ D.card := by omega
      have hd := total_domination_distance_bound G hG D hD u v
      nlinarith [Nat.mul_le_mul_right D.card hlarge]

omit [DecidableEq V] in
/-- A minimum total dominating set really exists on the stated connected nontrivial domain. -/
lemma exists_minimum_total_set (G : SimpleGraph V) [Nontrivial V]
    (hG : G.Connected) :
    ∃ D : Finset V, G.IsTotalDominating (D : Set V) ∧ D.card = G.totalDominationNumber := by
  classical
  have hU : G.IsTotalDominating ((Finset.univ : Finset V) : Set V) := by
    intro v
    have hv : v ∈ G.support := by rw [hG.preconnected.support_eq_univ]; trivial
    obtain ⟨w, hvw⟩ := G.mem_support.mp hv
    exact ⟨w, Finset.mem_univ _, hvw⟩
  have hne : ({n | ∃ D : Finset V, G.IsTotalNDominatingSet n D} : Set ℕ).Nonempty :=
    ⟨Fintype.card V, Finset.univ, hU, by simp⟩
  obtain ⟨D, hD, hc⟩ := Nat.sInf_mem hne
  exact ⟨D, hD, hc⟩

/-- The exact square-root ceiling statement of WOWII271. Distances are in G. -/
theorem conjecture271 (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G.Connected) :
    let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
    let dM := (M ×ˢ M).sup fun p => G.dist p.1 p.2
    ⌈Real.sqrt (2 * dM : ℝ)⌉₊ ≤ G.totalDominationNumber := by
  classical
  dsimp only
  let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
  let dM := (M ×ˢ M).sup fun p => G.dist p.1 p.2
  change ⌈Real.sqrt (2 * dM : ℝ)⌉₊ ≤ G.totalDominationNumber
  obtain ⟨D, hD, hc⟩ := exists_minimum_total_set G hG
  have hsup : dM ≤ D.card ^ 2 / 2 := by
    apply Finset.sup_le
    intro p hp
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hp
    have h := squared_bound_for_set G hG D hD p.1 p.2
      (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    omega
  have hsq : 2 * dM ≤ G.totalDominationNumber ^ 2 := by
    rw [hc] at hsup
    omega
  apply Nat.ceil_le.mpr
  apply (Real.sqrt_le_left (by positivity)).mpr
  exact_mod_cast hsq

end WOWII271Proof
