import FormalConjectures.WrittenOnTheWallII.GraphConjecture91

/-! Complete disproof using the actual 14-vertex witness. The proof establishes
b >= 12, f <= 10 and every local independence number <= 2. The finite cover
of three-vertex deletions is kernel-reduced, not native evaluation.
No infinite-family or global minimality claim is made. OpenAI Codex assisted. -/
namespace WOWII91Proof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture91

instance : DecidableRel witnessGraph.Adj := fun i j => by
  unfold witnessGraph
  infer_instance

def side (v u : Fin 14) : Bool :=
  (witnessEndpoints u).1 == (witnessEndpoints v).1 ||
    (witnessEndpoints u).2 == (witnessEndpoints v).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma same_side_adj : ∀ v u w : Fin 14,
    witnessGraph.Adj v u → witnessGraph.Adj v w →
    side v u = side v w → u ≠ w → witnessGraph.Adj u w := by decide

lemma local_independence_le (v : Fin 14) :
    (witnessGraph.induce (witnessGraph.neighborSet v)).indepNum ≤ 2 := by
  classical
  obtain ⟨S, hS⟩ := SimpleGraph.exists_isNIndepSet_indepNum
    (G := witnessGraph.induce (witnessGraph.neighborSet v))
  have hi : Set.InjOn (fun u : witnessGraph.neighborSet v => side v u.val) (S : Set _) := by
    intro a ha b hb heq
    by_contra hne
    have hne' : a.val ≠ b.val := fun he => hne (Subtype.ext he)
    exact hS.isIndepSet ha hb hne (same_side_adj v a.val b.val a.property b.property heq hne')
  calc
    (witnessGraph.induce (witnessGraph.neighborSet v)).indepNum = S.card := hS.card_eq.symm
    _ = (S.image fun u => side v u.val).card := (card_image_of_injOn hi).symm
    _ ≤ Fintype.card Bool := card_le_univ _
    _ = 2 := rfl

def bipartiteSet : Finset (Fin 14) := univ.filter fun v => v.val < 12

lemma bipartiteSet_card : bipartiteSet.card = 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma bipartite_colors : ∀ u v : Fin 14, u ∈ bipartiteSet → v ∈ bipartiteSet →
    witnessGraph.Adj u v → u.val % 2 ≠ v.val % 2 := by decide

lemma bipartiteSet_isBipartite :
    (witnessGraph.induce (bipartiteSet : Set (Fin 14))).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨v.val.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
  intro u v huv
  exact fun he => bipartite_colors u.val v.val u.property v.property huv (congrArg Fin.val he)

lemma bipartite_lower : 12 ≤ bipartiteNumber witnessGraph := by
  unfold bipartiteNumber
  apply le_csSup
  · refine ⟨14, ?_⟩
    rintro k ⟨A, hA, _⟩
    simpa [← hA] using card_le_univ A
  · exact ⟨bipartiteSet, bipartiteSet_card, bipartiteSet_isBipartite⟩

lemma cycle_three_false {V : Type*} (G : SimpleGraph V) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (eab : G.Adj a b) (ebc : G.Adj b c) (eca : G.Adj c a) : ¬ G.IsAcyclic := by
  intro h
  apply h (.cons eab (.cons ebc (.cons eca .nil)))
  simp [Walk.cons_isCycle_iff, Walk.isPath_def, Sym2.eq_iff,
    hab, hab.symm, hac, hac.symm, hbc, hbc.symm]

lemma cycle_four_false {V : Type*} (G : SimpleGraph V) (a b c d : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (eab : G.Adj a b) (ebc : G.Adj b c) (ecd : G.Adj c d) (eda : G.Adj d a) :
    ¬ G.IsAcyclic := by
  intro h
  apply h (.cons eab (.cons ebc (.cons ecd (.cons eda .nil))))
  simp [Walk.cons_isCycle_iff, Walk.isPath_def, Sym2.eq_iff,
    hab, hab.symm, hac, hac.symm, had, had.symm,
    hbc, hbc.symm, hbd, hbd.symm, hcd, hcd.symm]

def forbiddenCycles : Finset (Finset (Fin 14)) :=
  {{0, 1, 2, 3}, {4, 5, 6, 7}, {8, 9, 10, 11}, {0, 3, 12}, {4, 7, 12}, {4, 7, 13}, {4, 12, 13}, {7, 12, 13}, {8, 11, 13}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma deletion_cover : ∀ B ∈ (univ : Finset (Fin 14)).powersetCard 3,
    ∃ C ∈ forbiddenCycles, Disjoint B C := by decide

lemma forbidden_cycle_not_acyclic (A C : Finset (Fin 14))
    (hC : C ∈ forbiddenCycles) (hsub : C ⊆ A) :
    ¬ (witnessGraph.induce (A : Set (Fin 14))).IsAcyclic := by
  simp only [forbiddenCycles, mem_insert, mem_singleton] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · let a : (A : Set (Fin 14)) := ⟨0, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨1, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨2, hsub (by decide)⟩
    let d : (A : Set (Fin 14)) := ⟨3, hsub (by decide)⟩
    apply cycle_four_false _ a b c d
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · change witnessGraph.Adj 0 1
      decide
    · change witnessGraph.Adj 1 2
      decide
    · change witnessGraph.Adj 2 3
      decide
    · change witnessGraph.Adj 3 0
      decide
  · let a : (A : Set (Fin 14)) := ⟨4, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨5, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨6, hsub (by decide)⟩
    let d : (A : Set (Fin 14)) := ⟨7, hsub (by decide)⟩
    apply cycle_four_false _ a b c d
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · change witnessGraph.Adj 4 5
      decide
    · change witnessGraph.Adj 5 6
      decide
    · change witnessGraph.Adj 6 7
      decide
    · change witnessGraph.Adj 7 4
      decide
  · let a : (A : Set (Fin 14)) := ⟨8, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨9, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨10, hsub (by decide)⟩
    let d : (A : Set (Fin 14)) := ⟨11, hsub (by decide)⟩
    apply cycle_four_false _ a b c d
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c, d] at this
    · change witnessGraph.Adj 8 9
      decide
    · change witnessGraph.Adj 9 10
      decide
    · change witnessGraph.Adj 10 11
      decide
    · change witnessGraph.Adj 11 8
      decide
  · let a : (A : Set (Fin 14)) := ⟨0, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨3, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨12, hsub (by decide)⟩
    apply cycle_three_false _ a b c
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · change witnessGraph.Adj 0 3
      decide
    · change witnessGraph.Adj 3 12
      decide
    · change witnessGraph.Adj 12 0
      decide
  · let a : (A : Set (Fin 14)) := ⟨4, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨7, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨12, hsub (by decide)⟩
    apply cycle_three_false _ a b c
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · change witnessGraph.Adj 4 7
      decide
    · change witnessGraph.Adj 7 12
      decide
    · change witnessGraph.Adj 12 4
      decide
  · let a : (A : Set (Fin 14)) := ⟨4, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨7, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨13, hsub (by decide)⟩
    apply cycle_three_false _ a b c
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · change witnessGraph.Adj 4 7
      decide
    · change witnessGraph.Adj 7 13
      decide
    · change witnessGraph.Adj 13 4
      decide
  · let a : (A : Set (Fin 14)) := ⟨4, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨12, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨13, hsub (by decide)⟩
    apply cycle_three_false _ a b c
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · change witnessGraph.Adj 4 12
      decide
    · change witnessGraph.Adj 12 13
      decide
    · change witnessGraph.Adj 13 4
      decide
  · let a : (A : Set (Fin 14)) := ⟨7, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨12, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨13, hsub (by decide)⟩
    apply cycle_three_false _ a b c
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · change witnessGraph.Adj 7 12
      decide
    · change witnessGraph.Adj 12 13
      decide
    · change witnessGraph.Adj 13 7
      decide
  · let a : (A : Set (Fin 14)) := ⟨8, hsub (by decide)⟩
    let b : (A : Set (Fin 14)) := ⟨11, hsub (by decide)⟩
    let c : (A : Set (Fin 14)) := ⟨13, hsub (by decide)⟩
    apply cycle_three_false _ a b c
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · intro he
      have := congrArg Subtype.val he
      norm_num [a, b, c] at this
    · change witnessGraph.Adj 8 11
      decide
    · change witnessGraph.Adj 11 13
      decide
    · change witnessGraph.Adj 13 8
      decide

lemma forest_card_le (A : Finset (Fin 14))
    (hA : (witnessGraph.induce (A : Set (Fin 14))).IsAcyclic) : A.card ≤ 10 := by
  classical
  by_contra h
  obtain ⟨S, hSA, hS⟩ := exists_subset_card_eq (by omega : 11 ≤ A.card)
  let B : Finset (Fin 14) := univ \ S
  have hB : B ∈ (univ : Finset (Fin 14)).powersetCard 3 := by
    apply mem_powersetCard.mpr
    refine ⟨subset_univ _, ?_⟩
    simp [B, card_sdiff_of_subset (subset_univ S), hS]
  obtain ⟨C, hC, hBC⟩ := deletion_cover B hB
  apply forbidden_cycle_not_acyclic A C hC ?_ hA
  intro v hv
  apply hSA
  by_contra hn
  exact (disjoint_left.mp hBC) (by simp [B, hn]) hv

lemma forest_upper : forestNumber witnessGraph ≤ 10 := by
  unfold forestNumber
  apply csSup_le'
  rintro k ⟨A, rfl, hA⟩
  exact forest_card_le A hA

lemma connected : witnessGraph.Connected := by
  have h0 : ∀ v : Fin 14, witnessGraph.Reachable 0 v := by
    intro v
    fin_cases v
    · exact .rfl
    · exact (show witnessGraph.Adj 0 1 by decide).reachable
    · exact ((show witnessGraph.Adj 0 1 by decide).reachable).trans (show witnessGraph.Adj 1 2 by decide).reachable
    · exact (show witnessGraph.Adj 0 3 by decide).reachable
    · exact ((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 4 by decide).reachable
    · exact (((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 4 by decide).reachable).trans (show witnessGraph.Adj 4 5 by decide).reachable
    · exact (((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 7 by decide).reachable).trans (show witnessGraph.Adj 7 6 by decide).reachable
    · exact ((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 7 by decide).reachable
    · exact (((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 13 by decide).reachable).trans (show witnessGraph.Adj 13 8 by decide).reachable
    · exact ((((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 13 by decide).reachable).trans (show witnessGraph.Adj 13 8 by decide).reachable).trans (show witnessGraph.Adj 8 9 by decide).reachable
    · exact ((((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 13 by decide).reachable).trans (show witnessGraph.Adj 13 11 by decide).reachable).trans (show witnessGraph.Adj 11 10 by decide).reachable
    · exact (((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 13 by decide).reachable).trans (show witnessGraph.Adj 13 11 by decide).reachable
    · exact (show witnessGraph.Adj 0 12 by decide).reachable
    · exact ((show witnessGraph.Adj 0 12 by decide).reachable).trans (show witnessGraph.Adj 12 13 by decide).reachable
  exact ⟨fun u v => (h0 u).symm.trans (h0 v)⟩

lemma average_upper : averageLocalIndependence witnessGraph ≤ 2 := by
  unfold averageLocalIndependence
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 14)).mpr
  calc
    (∑ v : Fin 14, ((witnessGraph.induce (witnessGraph.neighborSet v)).indepNum : ℚ)) ≤
        ∑ _v : Fin 14, (2 : ℚ) := by
      apply sum_le_sum
      intro v _
      exact_mod_cast local_independence_le v
    _ = 2 * 14 := by norm_num

theorem conjecture91 : ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected →
    (bipartiteNumber G : ℚ) ≤ 1 + (forestNumber G : ℚ) *
      (⌈averageLocalIndependence G⌉₊ : ℚ) / 2 := by
  intro h
  have hbad := h 14 witnessGraph connected
  have hb : (12 : ℚ) ≤ bipartiteNumber witnessGraph := by exact_mod_cast bipartite_lower
  have hf : (forestNumber witnessGraph : ℚ) ≤ 10 := by exact_mod_cast forest_upper
  have hc : ⌈averageLocalIndependence witnessGraph⌉₊ ≤ 2 := Nat.ceil_le.mpr average_upper
  have hc' : (⌈averageLocalIndependence witnessGraph⌉₊ : ℚ) ≤ 2 := by exact_mod_cast hc
  have hm : (forestNumber witnessGraph : ℚ) * (⌈averageLocalIndependence witnessGraph⌉₊ : ℚ) ≤
      10 * 2 := mul_le_mul hf hc' (by positivity) (by norm_num)
  linarith

end WOWII91Proof

#print axioms WOWII91Proof.conjecture91
#print axioms WOWII91Proof.forest_card_le
#print axioms WOWII91Proof.local_independence_le
