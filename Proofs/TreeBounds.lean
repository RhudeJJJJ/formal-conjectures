import FormalConjectures.WrittenOnTheWallII.GraphConjecture348
import FormalConjectures.WrittenOnTheWallII.GraphConjecture367
import Lean.Util.CollectAxioms

/-!
General tree bounds for WOWII 348 and the positive reading of WOWII 367.
The proofs follow the written arguments of Jonas J. Gebendorfer, with Lean assistance
from OpenAI Codex. This development file is not a completed certificate until all
of its exported target theorems and their axiom audits compile.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Finset SimpleGraph

namespace WOWIITreeProof

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rowSum (S T : Finset V) : ℕ :=
  ∑ v ∈ S, (G.neighborFinset v ∩ T).card

lemma neighbor_inter_card (v : V) (T : Finset V) :
    (G.neighborFinset v ∩ T).card = ∑ w ∈ T, if G.Adj v w then 1 else 0 := by
  simp only [Finset.sum_boole]
  congr 1
  ext w
  simp [and_comm]

lemma row_sum_comm (S T : Finset V) : rowSum G S T = rowSum G T S := by
  simp only [rowSum, neighbor_inter_card]
  rw [Finset.sum_comm]
  simp only [G.adj_comm]

lemma degree_split (v : V) (D : Finset V) :
    G.degree v = (G.neighborFinset v ∩ D).card +
      (G.neighborFinset v ∩ Dᶜ).card := by
  rw [← G.card_neighborFinset_eq_degree]
  have hi : G.neighborFinset v ∩ Dᶜ = G.neighborFinset v \ D := by
    ext w
    simp
  rw [hi, Finset.card_inter_add_card_sdiff]

lemma internal_sum_even (D : Finset V) : Even (rowSum G D D) := by

  let H := G.induce (D : Set V)
  have he : ∀ v : (D : Set V),
      H.degree v = (G.neighborFinset v ∩ D).card := by
    intro v
    have hm := G.map_neighborFinset_induce (s := (D : Set V)) v
    have hc := congrArg Finset.card hm
    simp only [Finset.card_map, Finset.toFinset_coe] at hc
    convert hc using 1
    simp only [H, SimpleGraph.degree, SimpleGraph.neighborFinset, Set.toFinset_card,
      ← Nat.card_eq_fintype_card]
  have hs : rowSum G D D = ∑ v : (D : Set V), H.degree v := by
    simp only [rowSum, he]
    exact (Finset.sum_coe_sort D _).symm
  rw [hs, H.sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

lemma row_sum_lower (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (S : Finset V) : S.card ≤ rowSum G S D := by
  calc
    S.card = ∑ _ ∈ S, 1 := by simp
    _ ≤ rowSum G S D := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨w, hw, hadj⟩ := hD v
      exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
        ⟨w, Finset.mem_inter.mpr ⟨by simpa using hadj, hw⟩⟩)

def nonleaves : Finset V := Finset.univ.filter fun v => G.degree v ≠ 1

lemma total_degree_lower (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (S : Finset V) : S.card + (S.filter fun v => G.degree v ≠ 1).card ≤
      ∑ v ∈ S, G.degree v := by
  have hpos (v : V) : 1 ≤ G.degree v := by
    obtain ⟨w, hw, hadj⟩ := hD v
    exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
      ⟨w, by simpa using hadj⟩)
  calc
    S.card + (S.filter fun v => G.degree v ≠ 1).card =
        ∑ v ∈ S, (1 + if G.degree v ≠ 1 then 1 else 0) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      exact (Finset.sum_boole (s := S) (p := fun v => G.degree v ≠ 1)).symm
    _ ≤ ∑ v ∈ S, G.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      have hp := hpos v
      split_ifs <;> omega

lemma nonleaf_internal_bound (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) :
    (nonleaves G).card + rowSum G D D + 2 ≤ 3 * D.card := by

  have ht := hT.card_edgeFinset
  have handshake := G.sum_degrees_eq_twice_card_edges
  have hpartition := Finset.sum_add_sum_compl D (fun v => G.degree v)
  have hcard := Finset.card_add_card_compl D
  have hcross := row_sum_lower G D hD Dᶜ
  have hswap := row_sum_comm G D Dᶜ
  have hsplit : (∑ v ∈ D, G.degree v) = rowSum G D D + rowSum G D Dᶜ := by
    simp only [rowSum, ← Finset.sum_add_distrib, ← degree_split]
  have hx := total_degree_lower G D hD Dᶜ
  have hn : (nonleaves G).card ≤ D.card +
      (Dᶜ.filter fun v => G.degree v ≠ 1).card := by
    apply (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro v hv
    by_cases hd : v ∈ D
    · exact Finset.mem_union_left _ hd
    · exact Finset.mem_union_right _ (by simpa [nonleaves, hd] using hv)
  omega

lemma positive_degree (D : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (v : V) : 1 ≤ G.degree v := by
  obtain ⟨w, hw, hadj⟩ := hD v
  exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
    ⟨w, by simpa using hadj⟩)

lemma leaf_identity (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) :
    (Finset.univ.filter fun v => G.degree v = 1).card =
      2 + ∑ v : V, (G.degree v - 2) := by
  have ht := hT.card_edgeFinset
  have handshake := G.sum_degrees_eq_twice_card_edges
  have hp (v : V) : G.degree v + (if G.degree v = 1 then 1 else 0) =
      2 + (G.degree v - 2) := by
    have := positive_degree G D hD v
    split_ifs <;> omega
  have hs : (∑ v : V, G.degree v) +
      (Finset.univ.filter fun v => G.degree v = 1).card =
      2 * Fintype.card V + ∑ v : V, (G.degree v - 2) := by
    calc
      _ = ∑ v : V, (G.degree v + if G.degree v = 1 then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_boole]
        norm_cast
      _ = ∑ v : V, (2 + (G.degree v - 2)) := Finset.sum_congr rfl (fun v _ => hp v)
      _ = _ := by simp [Finset.sum_add_distrib]; omega
  omega

lemma triangular_lower (S : Finset ℕ) (hS : ∀ a ∈ S, 3 ≤ a) :
    S.card * (S.card + 1) ≤ 2 * ∑ a ∈ S, (a - 2) := by

  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hn : S.Nonempty
    · let a := S.max' hn
      have ha : a ∈ S := S.max'_mem hn
      have hsmall : S.erase a ⊂ S := Finset.erase_ssubset ha
      have hi := ih (S.erase a) hsmall (fun b hb => hS b (Finset.mem_of_mem_erase hb))
      have hsub : S ⊆ Finset.Icc 3 a := by
        intro b hb
        exact Finset.mem_Icc.mpr ⟨hS b hb, Finset.le_max' S b hb⟩
      have hc := Finset.card_le_card hsub
      have hca := Finset.card_erase_add_one ha
      have hsum := Finset.sum_erase_add S (fun a : ℕ => a - 2) ha
      have hapos := hS a ha
      simp only [Nat.card_Icc] at hc
      have hcsub : S.card ≤ a - 2 := by omega
      nlinarith
    · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [this]

lemma degree_diversity_bound (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V))
    (hcomp : WrittenOnTheWallII.GraphConjecture367.degreeCount G 1 <
      WrittenOnTheWallII.GraphConjecture367.degreeCount G 2) :
    (WrittenOnTheWallII.GraphConjecture367.distinctDegreeCount G) ^ 2 + 4 ≤
      2 * (nonleaves G).card +
        WrittenOnTheWallII.GraphConjecture367.distinctDegreeCount G := by

  let L := Finset.univ.filter fun v => G.degree v = 1
  let N := Finset.univ.filter fun v => G.degree v = 2
  let H := Finset.univ.filter fun v => 3 ≤ G.degree v
  let A := Finset.univ.image fun v => G.degree v
  let K := (A.erase 1).erase 2
  have hleaf := leaf_identity G hT D hD
  change L.card = 2 + ∑ v : V, (G.degree v - 2) at hleaf
  change L.card < N.card at hcomp
  have hlpos : 0 < L.card := by omega
  have hnpos : 0 < N.card := by omega
  obtain ⟨vl, hvl⟩ := Finset.card_pos.mp hlpos
  obtain ⟨vn, hvn⟩ := Finset.card_pos.mp hnpos
  have hvl' : G.degree vl = 1 := (Finset.mem_filter.mp hvl).2
  have hvn' : G.degree vn = 2 := (Finset.mem_filter.mp hvn).2
  have h1 : 1 ∈ A := Finset.mem_image.mpr ⟨vl, Finset.mem_univ _, hvl'⟩
  have h2 : 2 ∈ A.erase 1 := by
    simp only [Finset.mem_erase, ne_eq]
    exact ⟨by decide, Finset.mem_image.mpr ⟨vn, Finset.mem_univ _, hvn'⟩⟩
  have hcard1 := Finset.card_erase_add_one h1
  have hcard2 := Finset.card_erase_add_one h2
  have hksub : K ⊆ A := by intro k hk; exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)
  have hkpos : ∀ k ∈ K, 3 ≤ k := by
    intro k hk
    have hk2 := (Finset.mem_erase.mp hk).1
    have hk1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp (hksub hk)
    have hp := positive_degree G D hD v
    omega
  have htriangle := triangular_lower K hkpos
  have hsum1 : (∑ k ∈ K, (k - 2)) ≤ ∑ k ∈ A, (k - 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hksub (fun _ _ _ => Nat.zero_le _)
  have hsum2 : (∑ k ∈ A, (k - 2)) ≤ ∑ v : V, (G.degree v - 2) := by
    exact Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)

  have himage : K ⊆ H.image (fun v => G.degree v) := by
    intro k hk
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp (hksub hk)
    exact Finset.mem_image.mpr ⟨v, by simp [H, heq, hkpos k hk], heq⟩
  have hhigh : K.card ≤ H.card :=
    (Finset.card_le_card himage).trans Finset.card_image_le
  have hdisj : Disjoint N H := by
    apply Finset.disjoint_left.mpr
    intro v hv hn
    have h2 := (Finset.mem_filter.mp hv).2
    have h3 := (Finset.mem_filter.mp hn).2
    omega
  have hunion : N ∪ H ⊆ nonleaves G := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have h2 := (Finset.mem_filter.mp hv).2
      simp [nonleaves, h2]
    · have h3 := (Finset.mem_filter.mp hv).2
      simp only [nonleaves, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  have hnonleaf : N.card + H.card ≤ (nonleaves G).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  change A.card ^ 2 + 4 ≤ 2 * (nonleaves G).card + A.card
  change K.card + 1 = (A.erase 1).card at hcard2
  nlinarith

lemma positive_bound_set (hT : G.IsTree) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V))
    (hcomp : WrittenOnTheWallII.GraphConjecture367.degreeCount G 1 <
      WrittenOnTheWallII.GraphConjecture367.degreeCount G 2) :
    4 * WrittenOnTheWallII.GraphConjecture367.distinctDegreeCount G ≤ 3 * D.card := by
  have hn := nonleaf_internal_bound G hT D hD
  have hi := row_sum_lower G D hD D
  have hq := degree_diversity_bound G hT D hD hcomp
  let d := WrittenOnTheWallII.GraphConjecture367.distinctDegreeCount G
  have hquad : d * d + 8 ≤ 4 * D.card + d := by
    change d ^ 2 + 4 ≤ 2 * (nonleaves G).card + d at hq
    nlinarith
  by_cases hl : 5 ≤ d
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hl
    change 4 * d ≤ 3 * D.card
    rw [hk] at hquad ⊢
    nlinarith
  have hd : d = 2 ∨ d = 3 ∨ d = 4 := by
    have hleaf := leaf_identity G hT D hD
    have h2 : 2 ≤ d := by

      have hne : ∃ v : V, G.degree v = 1 := by
        have hp : 0 < (Finset.univ.filter fun v => G.degree v = 1).card := by omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hp
        exact ⟨v, (Finset.mem_filter.mp hv).2⟩
      have hn2 : ∃ v : V, G.degree v = 2 := by
        have hc : 0 < WrittenOnTheWallII.GraphConjecture367.degreeCount G 2 := by
          have hc1 : 0 < WrittenOnTheWallII.GraphConjecture367.degreeCount G 1 := by
            obtain ⟨v, hv⟩ := hne
            exact Finset.card_pos.mpr ⟨v, by simp [hv]⟩
          omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hc
        exact ⟨v, (Finset.mem_filter.mp hv).2⟩
      obtain ⟨v, hv⟩ := hne
      obtain ⟨w, hw⟩ := hn2
      have hsub : ({1, 2} : Finset ℕ) ⊆ Finset.univ.image (fun v => G.degree v) := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩,
          Finset.mem_image.mpr ⟨w, Finset.mem_univ _, hw⟩⟩
      have := Finset.card_le_card hsub
      simpa [d, WrittenOnTheWallII.GraphConjecture367.distinctDegreeCount] using this
    omega
  change 4 * d ≤ 3 * D.card
  rcases hd with hd | hd | hd
  · rw [hd] at hquad ⊢
    norm_num at hquad ⊢
    omega
  · rw [hd] at hquad ⊢
    norm_num at hquad ⊢
    omega
  · change d ^ 2 + 4 ≤ 2 * (nonleaves G).card + d at hq
    rw [hd] at hq ⊢
    have hnonleaf : 8 ≤ (nonleaves G).card := by norm_num at hq; omega
    obtain ⟨k, hk⟩ := internal_sum_even G D
    omega

theorem positive_367 (hT : G.IsTree) (hcard : 2 < Fintype.card V)
    (hmode : WrittenOnTheWallII.GraphConjecture367.TwoIsUniqueMode G) :
    4 * WrittenOnTheWallII.GraphConjecture367.distinctDegreeCount G ≤
      3 * G.totalDominationNumber := by

  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hfull : G.IsTotalDominating (Finset.univ : Finset V) := by
    intro v
    have hpos : 0 < G.degree v :=
      lt_of_lt_of_le hT.preconnected.minDegree_pos_of_nontrivial (G.minDegree_le_degree v)
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    exact ⟨w, Finset.mem_univ _, by simpa using hw⟩
  have hne : {n | ∃ D : Finset V, G.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, hfull, by simp⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hc := hmode.2 v (by omega)
  rw [hv] at hc
  have hbound := positive_bound_set G hT D hD.isTotalDominating hc
  have hsize := hD.card_eq
  change D.card = G.totalDominationNumber at hsize
  simpa [hsize] using hbound

end WOWIITreeProof

#print axioms WOWIITreeProof.positive_367

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``WOWIITreeProof.positive_367, ``WOWIITreeProof.degree_diversity_bound, ``WOWIITreeProof.positive_bound_set] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless allowed.contains ax do
        Lean.throwError m!"Unexpected axiom in {target}: {ax}"
    Lean.logInfo m!"Checked {target}: {axioms}"
  let negative ← Lean.collectAxioms ``sorryAx
  unless negative.contains ``sorryAx && !(negative.all allowed.contains) do
    Lean.throwError "Placeholder negative control was not rejected"
  Lean.logInfo "WOWII367_FULL_PROOF_PASS"
