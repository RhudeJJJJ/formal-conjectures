import Proofs.EdgePartitionCounts

/-!
# The exact edge budget outside a total dominating set

Source: Gebendorfer, Maximum-degree components and degree diversity in totally
dominated trees, 14 October 2026, Lemmas 3--5.
-/
namespace TotalDominationForestBudget
open SimpleGraph Finset ForestCounting EdgePartitionCounts
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V) [DecidableRel T.Adj]

lemma components_union_le (hT : T.IsAcyclic) (I U : Finset V) (hd : Disjoint I U) :
    components T (I ∪ U) ≤ components T I + components T U := by
  have hdis : Disjoint (innerEdges T I) (innerEdges T U) := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro hi hu
      exact Finset.disjoint_left.mp hd ((mem_innerEdges T I a b).mp hi).2.1
        ((mem_innerEdges T U a b).mp hu).2.1
  have hsub : innerEdges T I ∪ innerEdges T U ⊆ innerEdges T (I ∪ U) :=
    union_subset (innerEdges_mono T subset_union_left) (innerEdges_mono T subset_union_right)
  have he := card_le_card hsub
  rw [card_union_of_disjoint hdis] at he
  have hI := forest_on T hT I
  have hU := forest_on T hT U
  have hIU := forest_on T hT (I ∪ U)
  rw [card_union_of_disjoint hd] at hIU
  omega

lemma exact_budget (hT : T.IsTree) (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) :
    (innerEdges T (univ \ D)).card +
      (∑ x ∈ univ \ D, (into T D x - 1)) + 1 = components T D := by
  classical
  let X := univ \ D
  have hpos : ∀ x ∈ X, 1 ≤ into T D x := by
    intro x _
    obtain ⟨w,hw,hxw⟩ := hD x
    exact card_pos.mpr ⟨w,mem_inter.mpr ⟨by simpa using hxw,hw⟩⟩
  have hs : (∑ x ∈ X, (into T D x - 1)) + X.card = ∑ x ∈ X, into T D x := by
    calc
      _ = ∑ x ∈ X, ((into T D x - 1) + 1) := by simp [sum_add_distrib]
      _ = _ := sum_congr rfl (fun x hx => Nat.sub_add_cancel (hpos x hx))
  have hep := edge_partition T X D sdiff_disjoint
  have hu : X ∪ D = univ := sdiff_union_of_subset (subset_univ D)
  rw [hu] at hep
  have huniv : innerEdges T univ = T.edgeFinset := by simp [innerEdges]
  rw [huniv] at hep
  have hf := forest_on T hT.isAcyclic D
  have ht := hT.card_edgeFinset
  have hn : X.card + D.card = Fintype.card V := by
    simpa [X] using card_sdiff_add_card_eq_card (subset_univ D)
  dsimp [X] at hs hep hn hpos
  omega

lemma outside_degree (hT : T.IsTree) (D : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) {x : V} (hx : x ∉ D) :
    T.degree x ≤ components T D := by
  let X := univ \ D
  have hxX : x ∈ X := by simp [X,hx]
  have hi := into_le_edges T X hxX
  have hs := single_le_sum (fun y _ => Nat.zero_le (into T D y - 1)) hxX
  have he := exact_budget T hT D hD
  have hd := degree_split T D x
  obtain ⟨w,hw,hxw⟩ := hD x
  have hp : 1 ≤ into T D x := card_pos.mpr
    ⟨w,mem_inter.mpr ⟨by simpa using hxw,hw⟩⟩
  change (into T D x - 1) ≤ ∑ y ∈ X, (into T D y - 1) at hs
  change (innerEdges T X).card + _ + 1 = _ at he
  dsimp [X] at hi hs he hd
  omega

lemma maximum_outside_budget (hT : T.IsTree) (D U : Finset V)
    (hD : T.IsTotalDominating (D : Set V)) (hUD : Disjoint U D)
    (delta : ℕ) (hdelta : 2 ≤ delta) (hU : ∀ u ∈ U, T.degree u = delta) :
    U.card * (delta - 2) + components T U + 1 ≤ components T D := by
  let X := univ \ D
  have hUX : U ⊆ X := by
    intro u hu
    exact mem_sdiff.mpr ⟨mem_univ _,fun hd => Finset.disjoint_left.mp hUD hu hd⟩
  have hi := internal_degree_le T U X hUX
  have hf := forest_on T hT.isAcyclic U
  have he := exact_budget T hT D hD
  have hs : (∑ u ∈ U, (into T D u - 1)) + U.card = ∑ u ∈ U, into T D u := by
    calc
      _ = ∑ u ∈ U, ((into T D u - 1) + 1) := by simp [sum_add_distrib]
      _ = _ := by
        apply sum_congr rfl
        intro u _
        obtain ⟨w,hw,huw⟩ := hD u
        exact Nat.sub_add_cancel (card_pos.mpr ⟨w,mem_inter.mpr ⟨by simpa using huw,hw⟩⟩)
  have hsumle : (∑ u ∈ U, (into T D u - 1)) ≤ ∑ u ∈ X, (into T D u - 1) :=
    sum_le_sum_of_subset hUX
  have hsum : U.card * delta = (∑ u ∈ U, into T X u) + ∑ u ∈ U, into T D u := by
    calc
      _ = ∑ u ∈ U, delta := by simp
      _ = ∑ u ∈ U, T.degree u := sum_congr rfl (fun u hu => (hU u hu).symm)
      _ = _ := by
        simp_rw [degree_split T D, add_comm (into T D _) (into T (univ \ D) _)]
        rw [sum_add_distrib]
  have hmul : U.card * delta = U.card * (delta - 2) + 2 * U.card := by
    have hd : delta = (delta - 2) + 2 := by omega
    calc
      _ = U.card * ((delta - 2) + 2) := congrArg (U.card * ·) hd
      _ = _ := by rw [mul_add]; omega
  change (innerEdges T X).card + _ + 1 = _ at he
  dsimp [X] at hi he hsumle hsum
  omega

end TotalDominationForestBudget
