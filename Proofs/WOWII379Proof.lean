import FormalConjectures.WrittenOnTheWallII.GraphConjecture379
import Proofs.TotalDominationForestBudget

/-!
# WOWII 379 and its stronger total-set inequality

Source: Gebendorfer, Maximum-degree components and degree diversity in totally
dominated trees, 14 October 2026. The exact edge budget is formalized separately.
The degree-two case follows from the same budget and does not assume a path
classification theorem.
-/
namespace WOWII379Proof
open SimpleGraph Finset ForestCounting EdgePartitionCounts TotalDominationForestBudget
open WrittenOnTheWallII.GraphConjecture379
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma diversity_le (T : SimpleGraph V) [DecidableRel T.Adj] (b : ℕ)
    (hp : ∀ v, 1 ≤ T.degree v) (hb : ∀ v, T.degree v ≤ b) : degreeDiversity T ≤ b := by
  have hsub : univ.image (fun v => T.degree v) ⊆ Icc 1 b := by
    intro d hd
    obtain ⟨v,_,rfl⟩ := mem_image.mp hd
    exact mem_Icc.mpr ⟨hp v,hb v⟩
  have hc := card_le_card hsub
  simpa [degreeDiversity] using hc

omit [Fintype V] in
lemma total_card_two (T : SimpleGraph V) [Nonempty V] (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) : 2 ≤ D.card := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w,hw,_⟩ := hD v
  obtain ⟨u,hu,hwu⟩ := hD w
  have hs : {w,u} ⊆ D := insert_subset_iff.mpr ⟨hw,singleton_subset_iff.mpr hu⟩
  have hc := card_le_card hs
  simpa [hwu.ne] using hc

omit [DecidableEq V] in
lemma minimum_total_set (T : SimpleGraph V) (hT : T.IsTree)
    (horder : 1 < Fintype.card V) :
    ∃ D : Finset V, T.IsTotalDominating (D : Set V) ∧ D.card = T.totalDominationNumber := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp horder
  have hh : {n | ∃ D : Finset V, T.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card V,univ,?_,card_univ⟩
    intro v
    obtain ⟨w,hw⟩ := hT.preconnected.exists_adj_of_nontrivial v
    exact ⟨w,mem_univ _,hw⟩
  obtain ⟨D,hD⟩ := Nat.sInf_mem hh
  exact ⟨D,hD.isTotalDominating,hD.card_eq⟩

/-- The two integer counts underlying both rational target inequalities. -/
lemma degree_counts (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) :
    components T (maximumVertices T) + 1 ≤ D.card ∧
      degreeDiversity T + 2 * components T (maximumVertices T) ≤ 2 * D.card + 1 := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let M := maximumVertices T
  let X := univ \ D
  let I := M ∩ D
  let U := M \ D
  let c := components T D
  let cM := components T M
  let b := components T U
  let delta := T.maxDegree
  have hp : ∀ v, 1 ≤ T.degree v := fun v => hT.preconnected.degree_pos_of_nontrivial v
  have hdelta : 2 ≤ delta := by
    by_contra hn
    have hdeg : ∀ v, T.degree v ≤ 1 := fun v => (T.degree_le_maxDegree v).trans (by omega)
    have hsum : (∑ v : V, T.degree v) ≤ Fintype.card V := by
      calc
        _ ≤ ∑ _v : V, 1 := sum_le_sum (fun v _ => hdeg v)
        _ = _ := by simp
    rw [T.sum_degrees_eq_twice_card_edges] at hsum
    have ht := hT.card_edgeFinset
    omega
  have hM : ∀ v, v ∈ M ↔ T.degree v = delta := by
    intro v
    simp only [M, maximumVertices, mem_filter, mem_univ, true_and]
    constructor
    · intro hv
      apply le_antisymm (T.degree_le_maxDegree v)
      exact T.maxDegree_le_of_forall_degree_le _ hv
    · intro hv w
      rw [hv]
      exact T.degree_le_maxDegree w
  have hcpos : 1 ≤ c := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    obtain ⟨w,hw,_⟩ := hD v
    let : Nonempty (D : Set V) := ⟨⟨w,hw⟩⟩
    change 0 < Nat.card (T.induce (D : Set V)).ConnectedComponent
    exact Nat.card_pos
  have hfD := forest_on T hT.isAcyclic D
  have hfM := forest_on T hT.isAcyclic M
  have hcI : components T I ≤ (innerEdges T D).card :=
    components_le_innerEdges T D I inter_subset_right (fun v _ => hD v)
  have hIU : I ∪ U = M := by ext v; simp only [I,U,mem_union,mem_inter,mem_sdiff]; tauto
  have hdIU : Disjoint I U := by
    apply Finset.disjoint_left.mpr
    intro v hvI hvU
    exact (mem_sdiff.mp hvU).2 (mem_inter.mp hvI).2
  have hcM := components_union_le T hT.isAcyclic I U hdIU
  rw [hIU] at hcM
  have hk := diversity_le T delta hp T.degree_le_maxDegree
  change (innerEdges T D).card + c = D.card at hfD
  change (innerEdges T M).card + cM = M.card at hfM
  change cM ≤ components T I + b at hcM
  change cM + 1 ≤ D.card ∧ degreeDiversity T + 2 * cM ≤ 2 * D.card + 1
  by_cases hdc : c < delta
  · have hMD : M ⊆ D := by
      intro v hv
      by_contra hvD
      have hout := outside_degree T hT D hD hvD
      rw [(hM v).mp hv] at hout
      omega
    have hcm : cM ≤ (innerEdges T D).card :=
      components_le_innerEdges T D M hMD (fun v _ => hD v)
    let J := D \ M
    have hj : J.card + M.card = D.card := card_sdiff_add_card_eq_card hMD
    have hdegrees : univ.image (fun v => T.degree v) ⊆ (Icc 1 c ∪ J.image (fun v => T.degree v)) ∪ {delta} := by
      intro d hd
      obtain ⟨v,_,rfl⟩ := mem_image.mp hd
      by_cases hvD : v ∈ D
      · by_cases hvM : v ∈ M
        · exact mem_union_right _ (by simp [(hM v).mp hvM])
        · exact mem_union_left _ (mem_union_right _
            (mem_image_of_mem (fun v => T.degree v) (mem_sdiff.mpr ⟨hvD,hvM⟩)))
      · exact mem_union_left _ (mem_union_left _
          (mem_Icc.mpr ⟨hp v,outside_degree T hT D hD hvD⟩))
    have hcard := (card_le_card hdegrees).trans (card_union_le _ _)
    have hcard2 := card_union_le (Icc 1 c) (J.image (fun v => T.degree v))
    have hcard3 : (J.image (fun v => T.degree v)).card ≤ J.card := card_image_le
    have hinterval : (Icc 1 c).card = c := by simp
    have hsingle : ({delta} : Finset ℕ).card = 1 := card_singleton delta
    change degreeDiversity T ≤ _ at hcard
    omega
  · have hcd : delta ≤ c := by omega
    have hU : ∀ u ∈ U, T.degree u = delta := fun u hu => (hM u).mp (mem_sdiff.mp hu).1
    have huD : Disjoint U D := sdiff_disjoint
    have hb := maximum_outside_budget T hT D U hD huD delta hdelta hU
    have hfU := forest_on T hT.isAcyclic U
    change U.card * (delta - 2) + b + 1 ≤ c at hb
    change (innerEdges T U).card + b = U.card at hfU
    have hmulnonneg : 0 ≤ U.card * (delta - 2) := Nat.zero_le _
    have hfirst : cM + 1 ≤ D.card := by omega
    refine ⟨hfirst,?_⟩
    by_cases htwo : delta = 2
    · rw [htwo] at hk
      omega
    · have hthree : 3 ≤ delta := by omega
      have hmul : 2 * b ≤ U.card * (delta - 2) + b := by
        have hh : b ≤ U.card * (delta - 2) := by
          calc
            b ≤ U.card := by omega
            _ = U.card * 1 := by omega
            _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
        omega
      omega

theorem conjecture379_strengthened (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 2 < Fintype.card V) (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) :
    (componentsOn T (maximumVertices T) : ℚ) + max 1 (((degreeDiversity T : ℚ)-1)/2) ≤
      (D.card : ℚ) := by
  obtain ⟨h1,h2⟩ := degree_counts T hT horder D hD
  have hq1 : (components T (maximumVertices T) : ℚ) + 1 ≤ D.card := by exact_mod_cast h1
  have hq2 : (degreeDiversity T : ℚ) + 2 * components T (maximumVertices T) ≤
      2 * D.card + 1 := by exact_mod_cast h2
  change (components T (maximumVertices T) : ℚ) + _ ≤ _
  rw [add_max]
  exact max_le hq1 (by linarith)

theorem conjecture379 (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (horder : 1 < Fintype.card V) :
    (componentsOn T (maximumVertices T) : ℚ) + (degreeDiversity T : ℚ) / 3 ≤
      T.totalDominationNumber := by
  classical
  obtain ⟨D,hD,hcard⟩ := minimum_total_set T hT horder
  by_cases hn : 2 < Fintype.card V
  · have hs := conjecture379_strengthened T hT hn D hD
    rw [hcard] at hs
    by_cases hk : degreeDiversity T ≤ 3
    · have hq : (degreeDiversity T : ℚ) ≤ 3 := by exact_mod_cast hk
      have hm : (1 : ℚ) ≤ max 1 (((degreeDiversity T : ℚ)-1)/2) := le_max_left _ _
      linarith
    · have hq : (3 : ℚ) ≤ degreeDiversity T := by exact_mod_cast (show 3 ≤ degreeDiversity T by omega)
      have hm : (((degreeDiversity T : ℚ)-1)/2) ≤ max 1 (((degreeDiversity T : ℚ)-1)/2) := le_max_right _ _
      linarith
  · have hn2 : Fintype.card V = 2 := by omega
    let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp horder
    have hd : ∀ v, T.degree v = 1 := by
      intro v
      have hp := hT.preconnected.degree_pos_of_nontrivial v
      have hu := T.degree_lt_card_verts v
      omega
    have hM : maximumVertices T = univ := by ext v; simp [maximumVertices,hd]
    have hdeg : degreeDiversity T = 1 := by
      unfold degreeDiversity
      have hh : (fun v => T.degree v) = (fun _ : V => 1) := funext hd
      rw [hh]
      simp only [image_const,univ_nonempty,card_singleton]
    have he : innerEdges T univ = T.edgeFinset := by simp [innerEdges]
    have hc := forest_on T hT.isAcyclic univ
    rw [he,card_univ] at hc
    have ht := hT.card_edgeFinset
    have hcomp : componentsOn T (maximumVertices T) = 1 := by
      change components T (maximumVertices T) = 1
      rw [hM]
      omega
    have htwo := total_card_two T D hD
    rw [hcard] at htwo
    rw [hcomp,hdeg]
    have hq : (2 : ℚ) ≤ T.totalDominationNumber := by exact_mod_cast htwo
    norm_num only [Nat.cast_one]
    linarith

end WOWII379Proof
