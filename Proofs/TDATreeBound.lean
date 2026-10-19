import Proofs.TDATreeColor
import Proofs.TDALeafCounts

/-! The exact tree covering estimate, obtained from the two neighborhood colors. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tree_total_domination_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (hn : 3 ≤ Fintype.card V) :
    2 * G.totalDominationNumber ≤ Fintype.card V + (leaves G).card := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨color, hcolor⟩ := tree_neighborhood_two_coloring G hG (by omega)
  let Q := univ \ supports G
  let Q0 := Q.filter (fun v => color v = 0)
  let Q1 := Q.filter (fun v => color v = 1)
  have hQpartition : Q0 ∪ Q1 = Q := by
    ext v
    simp only [Q0, Q1, mem_union, mem_filter]
    have hc : color v = 0 ∨ color v = 1 := by omega
    tauto
  have hQdis : Disjoint Q0 Q1 := by
    apply Finset.disjoint_left.mpr
    intro v hv0 hv1
    have h0 := (mem_filter.mp hv0).2
    have h1 := (mem_filter.mp hv1).2
    have hne : (0 : Fin 2) ≠ 1 := by decide
    exact hne (h0.symm.trans h1)
  have hQcard : Q0.card + Q1.card = Q.card := by
    rw [← card_union_of_disjoint hQdis, hQpartition]
  have hQS : Q.card + (supports G).card = Fintype.card V := by
    have hc := card_sdiff_add_card_eq_card (subset_univ (supports G))
    simpa only [Q, card_univ] using hc
  have hex : ∀ i : Fin 2, G.totalDominationNumber ≤
      (supports G).card + (Q.filter (fun v => color v = i)).card := by
    intro i
    let X := Q.filter (fun v => color v = i)
    let D := supports G ∪ X
    have hTD : G.IsTotalDominating (D : Set V) := by
      intro v
      by_cases hleaf : G.degree v = 1
      · obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
        have hwS : w ∈ supports G := mem_supports.mpr ⟨v, mem_leaves.mpr hleaf, hvw.symm⟩
        exact ⟨w, mem_union_left _ hwS, hvw⟩
      · have hp := hG.connected.preconnected.degree_pos_of_nontrivial v
        obtain ⟨w, hvw, hwc⟩ := hcolor v (by omega) i
        by_cases hwS : w ∈ supports G
        · exact ⟨w, mem_union_left _ hwS, hvw⟩
        · have hwX : w ∈ X := mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hwS⟩, hwc⟩
          exact ⟨w, mem_union_right _ hwX, hvw⟩
    have hle := totalDominationNumber_le_card G D hTD
    have hc : D.card ≤ (supports G).card + X.card := card_union_le _ _
    exact hle.trans hc
  have h0 := hex 0
  have h1 := hex 1
  change G.totalDominationNumber ≤ (supports G).card + Q0.card at h0
  change G.totalDominationNumber ≤ (supports G).card + Q1.card at h1
  have hSL := supports_card_le_leaves G hG.connected.preconnected hn
  omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.tree_total_domination_bound
