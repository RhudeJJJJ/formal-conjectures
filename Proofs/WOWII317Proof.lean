/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LargestInducedTree
import Mathlib.Tactic


/-!
# A complete proof of Written on the Wall II Conjecture 317

Author: Jonas J. Gebendorfer. OpenAI Codex assisted with formalization.
Written source: *Three Well-Total-Domination Conjectures from the Written on the Wall II List*,
28 July 2026, Theorem 4.5, https://doi.org/10.5281/zenodo.21650036.

The exact repository statement is proved for every finite simple connected graph with
more than one vertex. A stronger theorem gives cardinality two for every minimal total
dominating set. The proof uses private neighbors and complement-edge counting, not a
bounded graph search. The four-edge exception is excluded by an induced-tree count.
-/

open SimpleGraph Finset

namespace WOWII317Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma edge_complement_sum (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  classical
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hg : G.Adj u v := by simpa using he
      have hgc : Gᶜ.Adj u v := by simpa using he'
      exact hgc.2 hg
  have hu : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      by_cases ha : G.Adj u v
      · simp [SimpleGraph.compl_adj, ha, ha.ne]
      · simp [SimpleGraph.compl_adj, ha]
  rw [← Finset.card_union_of_disjoint hd, hu]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

lemma tree_complement_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : (G.induce (s : Set V)).IsTree) :
    s.card.choose 2 + 1 = s.card +
      (Gᶜ.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card := by
  classical
  have heq : (G.induce (s : Set V))ᶜ = Gᶜ.induce (s : Set V) := by
    ext x y
    simp [SimpleGraph.compl_adj]
  have hecard : ((G.induce (s : Set V))ᶜ).edgeFinset.card =
      (Gᶜ.induce (s : Set V)).edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
    simpa only [Nat.card_eq_fintype_card] using
      congrArg (fun H : SimpleGraph (s : Set V) => Nat.card H.edgeSet) heq
  have hsum : (G.induce (s : Set V)).edgeFinset.card +
      (Gᶜ.induce (s : Set V)).edgeFinset.card = s.card.choose 2 := by
    simpa [hecard] using edge_complement_sum (G.induce (s : Set V))
  have htree : (G.induce (s : Set V)).edgeFinset.card + 1 = s.card := by
    simpa using hs.card_edgeFinset
  have hc := Gᶜ.card_filter_edgeFinset_toFinset_subset s
  omega

lemma tree_card_le_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : (G.induce (s : Set V)).IsTree)
    (h : Gᶜ.edgeFinset.card ≤ s.card) : s.card ≤ 4 := by
  have hcount := tree_complement_count G s hs
  have hfilter := Finset.card_filter_le Gᶜ.edgeFinset (fun e => e.toFinset ⊆ s)
  have hchoose : s.card.choose 2 ≤ 2 * s.card - 1 := by omega
  by_contra hn
  have hfive : 5 ≤ s.card := by omega
  rw [Nat.choose_two_right] at hchoose
  have hprod : s.card * (s.card - 1) ≤ 4 * s.card - 1 := by omega
  have hfour : 4 ≤ s.card - 1 := by omega
  have hl := Nat.mul_le_mul_left s.card hfour
  rw [Nat.mul_comm s.card 4] at hl
  omega

omit [Fintype V] in
lemma private_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : Finset V} (hD : G.IsMinimalTotalDominatingSet D) {a : V} (ha : a ∈ D) :
    ∃ x : V, G.Adj x a ∧ ∀ b ∈ D, G.Adj x b → b = a := by
  classical
  have herase : D.erase a ⊂ D := Finset.erase_ssubset ha
  have hnot := hD.2 (D.erase a) herase
  simp only [IsTotalDominatingSet, not_forall, not_exists, not_and] at hnot
  obtain ⟨x, hx⟩ := hnot
  obtain ⟨b, hb, hxb⟩ := hD.1 x
  have hba : b = a := by
    by_contra hne
    exact hx b (Finset.mem_erase.mpr ⟨hne, hb⟩) hxb
  subst b
  refine ⟨x, hxb, ?_⟩
  intro b hb hxb
  by_contra hne
  exact hx b (Finset.mem_erase.mpr ⟨hne, hb⟩) hxb

lemma five_missing_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (e₁ e₂ e₃ e₄ e₅ : Sym2 V)
    (hp : [e₁,e₂,e₃,e₄,e₅].Pairwise (· ≠ ·))
    (he : ∀ e ∈ [e₁,e₂,e₃,e₄,e₅], e ∈ Gᶜ.edgeFinset) :
    5 ≤ Gᶜ.edgeFinset.card := by
  have hsub : [e₁,e₂,e₃,e₄,e₅].toFinset ⊆ Gᶜ.edgeFinset := by
    intro e h
    exact he e (List.mem_toFinset.mp h)
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hp] at hc
  exact hc

lemma selected_neighbor_unique (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : Finset V} (hD : G.IsMinimalTotalDominatingSet D)
    (hm : Gᶜ.edgeFinset.card ≤ 4) {a b c : V}
    (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : G.Adj b a) (hbc : G.Adj b c) : a = c := by
  classical
  by_contra hac
  obtain ⟨x, hxa, hx⟩ := private_neighbor G hD ha
  obtain ⟨y, hyc, hy⟩ := private_neighbor G hD hc
  have hba := hab.ne
  have hbcne := hbc.ne
  have hxx : ∀ v : V, ¬ G.Adj v v := fun _ => G.irrefl
  have hsym : ∀ u v : V, G.Adj u v → G.Adj v u := fun _ _ h => h.symm
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact (Ne.symm hac) (hx c hc hyc)
  have hxb : ¬ G.Adj x b := by
    intro h
    exact hba (hx b hb h)
  have hxc : ¬ G.Adj x c := by
    intro h
    exact (Ne.symm hac) (hx c hc h)
  have hya : ¬ G.Adj y a := by
    intro h
    exact hac (hy a ha h)
  have hyb : ¬ G.Adj y b := by
    intro h
    exact hbcne (hy b hb h)
  have hxne : x ≠ a ∧ x ≠ b ∧ x ≠ c := by grind
  have hyne : y ≠ a ∧ y ≠ b ∧ y ≠ c := by grind
  by_cases hacadj : G.Adj a c
  · obtain ⟨z, hzb, hz⟩ := private_neighbor G hD hb
    have hza : ¬ G.Adj z a := by
      intro h
      exact hba.symm (hz a ha h)
    have hzxa : z ≠ x := by grind
    have hzya : z ≠ y := by grind
    have hzne : z ≠ a ∧ z ≠ b ∧ z ≠ c := by grind
    have hpair : [s(x,b),s(x,c),s(y,a),s(y,b),s(z,a)].Pairwise (· ≠ ·) := by
      simp
      grind
    have hmissing := five_missing_edges G s(x,b) s(x,c) s(y,a) s(y,b) s(z,a)
      hpair (by simp [SimpleGraph.compl_adj, hxne, hyne, hzne, hxb, hxc, hya, hyb, hza])
    omega
  · have hpair : [s(x,b),s(x,c),s(y,a),s(y,b),s(a,c)].Pairwise (· ≠ ·) := by
      simp
      grind
    have hmissing := five_missing_edges G s(x,b) s(x,c) s(y,a) s(y,b) s(a,c)
      hpair (by simp [SimpleGraph.compl_adj, hxne, hyne, hac, hxb, hxc, hya, hyb, hacadj])
    omega

lemma exists_largest_tree (G : SimpleGraph V) [Nonempty V] (hG : G.Connected) :
    ∃ s : Finset V, s.card = G.largestInducedTreeSize ∧
      (G.induce (s : Set V)).IsTree := by
  classical
  let x : V := Classical.choice inferInstance
  obtain ⟨t, _, _, ht⟩ := hG.exists_induced_tree_containing_pair x x
  have hne : {n | ∃ s : Finset V, s.card = n ∧ (G.induce (s : Set V)).IsTree}.Nonempty :=
    ⟨t.card, t, rfl, ht⟩
  have hfin : {n | ∃ s : Finset V, s.card = n ∧ (G.induce (s : Set V)).IsTree}.Finite := by
    apply (Set.finite_range (fun s : Finset V => s.card)).subset
    rintro n ⟨s, rfl, _⟩
    exact ⟨s, rfl⟩
  exact hne.csSup_mem hfin

lemma complement_card_le_four (G : SimpleGraph V) [Nonempty V] [DecidableRel G.Adj]
    (hG : G.Connected) (h : Gᶜ.edgeFinset.card ≤ G.largestInducedTreeSize) :
    Gᶜ.edgeFinset.card ≤ 4 := by
  obtain ⟨s, hcard, hs⟩ := exists_largest_tree G hG
  have hm : Gᶜ.edgeFinset.card ≤ s.card := by omega
  have hs4 := tree_card_le_four G s hs hm
  omega

lemma matching_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : Finset V} (hD : G.IsMinimalTotalDominatingSet D)
    (hm : Gᶜ.edgeFinset.card ≤ 4)
    {a b c d : V} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D)
    (hab : G.Adj a b) (hcd : G.Adj c d) (hac : c ≠ a) (hbc : c ≠ b) :
    Gᶜ.edgeFinset = {s(a,c),s(a,d),s(b,c),s(b,d)} ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  have hxx : ∀ v : V, ¬ G.Adj v v := fun _ => G.irrefl
  have hsym : ∀ u v : V, G.Adj u v → G.Adj v u := fun _ _ h => h.symm
  have huniq : ∀ {u v w : V}, u ∈ D → w ∈ D → v ∈ D →
      G.Adj w u → G.Adj w v → u = v := by
    intro u v w hu hw hv hwu hwv
    exact selected_neighbor_unique G hD hm hu hw hv hwu hwv
  have had : a ≠ d := by
    intro he
    subst d
    have heq := huniq hb ha hc hab hcd.symm
    exact hbc heq.symm
  have hbd : b ≠ d := by
    intro he
    subst d
    have heq := huniq ha hb hc hab.symm hcd.symm
    exact hac heq.symm
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    grind
  have hnac : ¬G.Adj a c := by
    intro he
    exact hbc (huniq hb ha hc hab he).symm
  have hnad : ¬G.Adj a d := by
    intro he
    exact hbd (huniq hb ha hd hab he)
  have hnbc : ¬G.Adj b c := by
    intro he
    exact hac (huniq ha hb hc hab.symm he).symm
  have hnbd : ¬G.Adj b d := by
    intro he
    exact had (huniq ha hb hd hab.symm he)
  let E : Finset (Sym2 V) := {s(a,c),s(a,d),s(b,c),s(b,d)}
  have hE : E ⊆ Gᶜ.edgeFinset := by
    simp [E, Finset.insert_subset_iff, Finset.singleton_subset_iff, SimpleGraph.compl_adj, hne, hnac, hnad, hnbc, hnbd]
  have hEc : E.card = 4 := by
    simp [E, hne, Ne.symm hne.2.2.2.2.2]
  have heq : E = Gᶜ.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le hE
    omega
  exact ⟨heq.symm, hne⟩

lemma exceptional_tree_card (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b c d : V}
    (he : Gᶜ.edgeFinset = {s(a,c),s(a,d),s(b,c),s(b,d)})
    (hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    {s : Finset V} (hs : (G.induce (s : Set V)).IsTree) : s.card ≤ 3 := by
  classical
  have hm : Gᶜ.edgeFinset.card = 4 := by
    simp [he, hne, Ne.symm hne.2.2.2.2.2]
  by_contra hn
  have hsge : 4 ≤ s.card := by omega
  have hsle := tree_card_le_four G s hs (by omega)
  have hs4 : s.card = 4 := by omega
  have hcount := tree_complement_count G s hs
  rw [hs4] at hcount
  rw [Nat.choose_two_right] at hcount
  norm_num at hcount
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s <;>
    by_cases hc : c ∈ s <;> by_cases hd : d ∈ s <;>
    simp [he, Finset.filter_insert, Finset.filter_singleton, Sym2.toFinset_mk_eq,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb, hc, hd, hne,
      Ne.symm hne.2.2.2.2.2] at hcount

theorem minimal_total_domination_card_two (G : SimpleGraph V)
    [Nontrivial V] [DecidableRel G.Adj] (hG : G.Connected)
    (h : Gᶜ.edgeFinset.card ≤ G.largestInducedTreeSize)
    {D : Finset V} (hD : G.IsMinimalTotalDominatingSet D) : D.card = 2 := by
  classical
  have hm := complement_card_le_four G hG h
  let v : V := Classical.choice inferInstance
  obtain ⟨a, ha, _⟩ := hD.1 v
  obtain ⟨b, hb, hab⟩ := hD.1 a
  have hsub : {a,b} ⊆ D := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, ha, hb]
  by_cases heq : D = {a,b}
  · simp [heq, hab.ne]
  · have hex : ∃ c ∈ D, c ≠ a ∧ c ≠ b := by
      by_contra hn
      apply heq
      apply Finset.Subset.antisymm
      · intro c hc
        by_contra hnot
        have hne : c ≠ a ∧ c ≠ b := by simpa using hnot
        exact hn ⟨c,hc,hne⟩
      · exact hsub
    obtain ⟨c, hc, hca, hcb⟩ := hex
    obtain ⟨d, hd, hcd⟩ := hD.1 c
    obtain ⟨he, hne⟩ := matching_complement G hD hm ha hb hc hd hab hcd hca hcb
    obtain ⟨s, hcard, hs⟩ := exists_largest_tree G hG
    have hsmall := exceptional_tree_card G he hne hs
    have hm4 : Gᶜ.edgeFinset.card = 4 := by
      simp [he, hne, Ne.symm hne.2.2.2.2.2]
    omega

/-- Every finite connected graph satisfying WOWII 317 is well totally dominated. -/
theorem conjecture317 {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (h : Gᶜ.edgeFinset.card ≤ G.largestInducedTreeSize) :
    G.IsWellTotallyDominated := by
  intro S T hS hT
  rw [minimal_total_domination_card_two G hG h hS,
    minimal_total_domination_card_two G hG h hT]

end WOWII317Proof

