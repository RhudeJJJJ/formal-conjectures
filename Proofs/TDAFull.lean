import Proofs.TDAMaxTwo
import Proofs.TDACycleEdge

/-! The universal total-domination--annihilation theorem, with the repository's
actual invariants and without extra graph hypotheses. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem target_order_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hn : Fintype.card V = 2) :
    G.totalDominationNumber ≤ G.annihilationNumber + 1 := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hTD : G.IsTotalDominating ((univ : Finset V) : Set V) := by
    intro v
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp
      (hG.preconnected.degree_pos_of_nontrivial v)
    exact ⟨w, mem_univ _, hvw⟩
  have hdom := totalDominationNumber_le_card G univ hTD
  simp only [card_univ, hn] at hdom
  obtain ⟨v⟩ := hG.nonempty
  have hb : ∑ w ∈ ({v} : Finset V), G.degree w ≤ G.edgeFinset.card := by
    simpa using G.degree_le_card_edgeFinset v
  have ha := card_le_annihilationNumber G {v} hb
  simp only [card_singleton] at ha
  omega

private theorem full_aux (n : ℕ) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeFinset.card ≤ n →
      G.Connected → 2 ≤ Fintype.card V →
      G.totalDominationNumber ≤ G.annihilationNumber + 1 := by
  classical
  induction n using Nat.strong_induction_on with
  | h n IH =>
    intro G _ hcard hG horder
    by_cases hn : 3 ≤ Fintype.card V
    · by_cases hlow : ∑ v ∈ lowVertices G, G.degree v ≤ G.edgeFinset.card
      · have hle := total_domination_le_annihilation_of_low_budget G hG hn hlow
        omega
      · have hlarge : G.edgeFinset.card < ∑ v ∈ lowVertices G, G.degree v := by omega
        by_cases htree : G.IsTree
        · have ht := tree_total_domination_bound G htree hn
          have he := htree.card_edgeFinset
          have ha := edges_add_leaves_le_twice_annihilation_add_one G hG hn hlarge
          omega
        · by_cases hmax : ∀ v, G.degree v ≤ 2
          · exact target_max_degree_two G hG hn htree hmax
          · have hhigh : ∃ v, 3 ≤ G.degree v := by
              push_neg at hmax
              obtain ⟨v, hv⟩ := hmax
              exact ⟨v, by omega⟩
            obtain ⟨u, v, huv, hvhigh, hnonbridge⟩ :=
              exists_nonbridge_high_endpoint G hG htree hhigh
            let H := G.deleteEdges {s(u, v)}
            have hH : H.Connected := hG.connected_delete_edge_of_not_isBridge hnonbridge
            have hc := edge_count_delete_edge G huv
            have hstrict : H.edgeFinset.card < n := by
              change H.edgeFinset.card + 1 = G.edgeFinset.card at hc
              omega
            have hIH := IH H.edgeFinset.card hstrict H le_rfl hH horder
            have hmono := total_domination_mono_connected G H (G.deleteEdges_le _) hH horder
            have ha := annihilation_delete_high_edge G huv hvhigh hlarge
            change H.annihilationNumber ≤ G.annihilationNumber at ha
            omega
    · have hn2 : Fintype.card V = 2 := by omega
      exact target_order_two G hG hn2

/-- Every finite simple connected graph on at least two vertices satisfies the
total-domination--annihilation inequality. This is the exact target of PR 7388. -/
theorem total_domination_annihilation (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (horder : 2 ≤ Fintype.card V) :
    G.totalDominationNumber ≤ G.annihilationNumber + 1 :=
  full_aux G.edgeFinset.card G le_rfl hG horder

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.total_domination_annihilation
