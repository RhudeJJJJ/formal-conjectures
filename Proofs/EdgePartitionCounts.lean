import Proofs.ForestCounting

/-! Exact induced and crossing edge counts for finite vertex sets. -/
namespace EdgePartitionCounts
open SimpleGraph Finset ForestCounting
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def into (A : Finset V) (v : V) : ℕ := (G.neighborFinset v ∩ A).card
def crossingAt (B : Finset V) (v : V) : Finset (Sym2 V) :=
  (G.neighborFinset v ∩ B).image fun w => s(v,w)

lemma crossingAt_card (B : Finset V) (v : V) :
    (crossingAt G B v).card = into G B v :=
  card_image_of_injective _ (fun _ _ h => Sym2.congr_right.mp h)

@[simp] lemma mem_crossingAt (B : Finset V) (v a b : V) :
    s(a,b) ∈ crossingAt G B v ↔
      (v = a ∧ G.Adj a b ∧ b ∈ B) ∨ (v = b ∧ G.Adj b a ∧ a ∈ B) := by
  simp only [crossingAt, mem_image, mem_inter, mem_neighborFinset, Sym2.eq_iff]
  aesop

lemma edge_partition (A B : Finset V) (hd : Disjoint A B) :
    (innerEdges G (A ∪ B)).card = (innerEdges G A).card + (innerEdges G B).card +
      ∑ v ∈ A, into G B v := by
  classical
  let C := A.biUnion (crossingAt G B)
  have hC : ∀ a b, s(a,b) ∈ C ↔
      G.Adj a b ∧ ((a ∈ A ∧ b ∈ B) ∨ (b ∈ A ∧ a ∈ B)) := by
    intro a b
    simp only [C, mem_biUnion, mem_crossingAt]
    constructor
    · rintro ⟨v,hv,(⟨rfl,hab,hb⟩ | ⟨rfl,hba,ha⟩)⟩
      · exact ⟨hab,Or.inl ⟨hv,hb⟩⟩
      · exact ⟨hba.symm,Or.inr ⟨hv,ha⟩⟩
    · rintro ⟨hab,(⟨ha,hb⟩ | ⟨hb,ha⟩)⟩
      · exact ⟨a,ha,Or.inl ⟨rfl,hab,hb⟩⟩
      · exact ⟨b,hb,Or.inr ⟨rfl,hab.symm,ha⟩⟩
  have hEq : innerEdges G (A ∪ B) = (innerEdges G A ∪ innerEdges G B) ∪ C := by
    ext e
    induction e using Sym2.ind with
    | _ a b => simp only [mem_union, mem_innerEdges, hC]; aesop
  have hdAB : Disjoint (innerEdges G A) (innerEdges G B) := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro ha hb
      exact Finset.disjoint_left.mp hd ((mem_innerEdges G A a b).mp ha).2.1
        ((mem_innerEdges G B a b).mp hb).2.1
  have hdC : Disjoint (innerEdges G A ∪ innerEdges G B) C := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he hc
      have hc' := (hC a b).mp hc
      rcases mem_union.mp he with ha | hb
      · have ha' := (mem_innerEdges G A a b).mp ha
        rcases hc'.2 with h | h
        · exact Finset.disjoint_left.mp hd ha'.2.2 h.2
        · exact Finset.disjoint_left.mp hd ha'.2.1 h.2
      · have hb' := (mem_innerEdges G B a b).mp hb
        rcases hc'.2 with h | h
        · exact Finset.disjoint_left.mp hd h.1 hb'.2.1
        · exact Finset.disjoint_left.mp hd h.1 hb'.2.2
  have hdisj : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      Disjoint (crossingAt G B u) (crossingAt G B v) := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he hf
      have h1 := (mem_crossingAt G B u a b).mp he
      have h2 := (mem_crossingAt G B v a b).mp hf
      rcases h1 with ⟨rfl,_,hb⟩ | ⟨rfl,_,ha⟩ <;>
        rcases h2 with ⟨rfl,_,hb'⟩ | ⟨rfl,_,ha'⟩
      · exact huv rfl
      · exact Finset.disjoint_left.mp hd hv hb
      · exact Finset.disjoint_left.mp hd hv ha
      · exact huv rfl
  rw [hEq, card_union_of_disjoint hdC, card_union_of_disjoint hdAB]
  congr 1
  dsimp [C]
  rw [card_biUnion hdisj]
  exact sum_congr rfl (fun v _ => crossingAt_card G B v)

lemma into_union (A B : Finset V) (hd : Disjoint A B) (v : V) :
    into G (A ∪ B) v = into G A v + into G B v := by
  unfold into
  rw [inter_union_distrib_left,card_union_of_disjoint]
  exact hd.mono inter_subset_right inter_subset_right

lemma into_induce (A : Finset V) (v : (A : Set V)) :
    (G.induce (A : Set V)).degree v = into G A v := by
  classical
  have h : ((G.induce (A : Set V)).neighborFinset v).image Subtype.val =
      G.neighborFinset v.val ∩ A := by ext w; simp
  unfold into
  rw [← card_neighborFinset_eq_degree,← h,card_image_of_injective _ Subtype.val_injective]

lemma into_self_sum (A : Finset V) :
    (∑ v ∈ A, into G A v) = 2 * (innerEdges G A).card := by
  classical
  have hh := (G.induce (A : Set V)).sum_degrees_eq_twice_card_edges
  simp_rw [into_induce] at hh
  rw [innerEdges,G.card_filter_edgeFinset_toFinset_subset]
  rw [Finset.sum_subtype A (fun _ => Iff.rfl) (fun v => into G A v)]
  exact hh

lemma into_univ (v : V) : into G univ v = G.degree v := by simp [into]

lemma degree_split (A : Finset V) (v : V) :
    G.degree v = into G A v + into G (univ \ A) v := by
  have hh := into_union G A (univ \ A) (disjoint_sdiff_self_right) v
  rw [union_sdiff_of_subset (subset_univ A),into_univ] at hh
  exact hh

lemma internal_degree_le (U X : Finset V) (hUX : U ⊆ X) :
    (∑ u ∈ U, into G X u) ≤ (innerEdges G U).card + (innerEdges G X).card := by
  have hd : Disjoint U (X \ U) := disjoint_sdiff_self_right
  have hu : U ∪ (X \ U) = X := union_sdiff_of_subset hUX
  have he := edge_partition G U (X \ U) hd
  rw [hu] at he
  have hs : (∑ u ∈ U, into G X u) =
      2 * (innerEdges G U).card + ∑ u ∈ U, into G (X \ U) u := by
    calc
      _ = ∑ u ∈ U, (into G U u + into G (X \ U) u) := by
        apply sum_congr rfl
        intro u _
        rw [← into_union G U (X \ U) hd,hu]
      _ = _ := by rw [sum_add_distrib,into_self_sum]
  omega

lemma into_le_edges (X : Finset V) {v : V} (hv : v ∈ X) :
    into G X v ≤ (innerEdges G X).card := by
  rw [← crossingAt_card]
  apply card_le_card
  intro e he
  obtain ⟨w,hw,rfl⟩ := mem_image.mp he
  have hh := mem_inter.mp hw
  exact (mem_innerEdges G X v w).mpr ⟨by simpa using hh.1,hv,hh.2⟩

lemma innerEdges_mono {A B : Finset V} (hab : A ⊆ B) :
    innerEdges G A ⊆ innerEdges G B := by
  intro e he
  exact mem_filter.mpr ⟨(mem_filter.mp he).1, ((mem_filter.mp he).2).trans hab⟩

end EdgePartitionCounts
