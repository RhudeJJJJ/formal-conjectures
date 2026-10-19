import Proofs.TDATreeBound
import Proofs.TDAGraphEdge

/-! Connected graphs of maximum degree two, through a spanning path. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem leaves_tree_max_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (hn : 2 ≤ Fintype.card V) (hmax : ∀ v, G.degree v ≤ 2) :
    (leaves G).card = 2 := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos := hG.connected.preconnected.degree_pos_of_nontrivial
  have hlow : lowVertices G = univ := by
    ext v
    simp only [lowVertices, mem_filter, mem_univ, true_and]
    exact iff_true_intro (hmax v)
  have hsum := low_vertices_sum G hpos
  rw [hlow, G.sum_degrees_eq_twice_card_edges] at hsum
  have hc : (leaves G).card + (degreeTwo G).card = Fintype.card V := by
    rw [← card_union_of_disjoint (leaves_disjoint_degreeTwo G), ← low_vertices_partition G hpos,
      hlow, card_univ]
  have htree := hG.card_edgeFinset
  omega

/-- The maximum-degree-two case is covered by its spanning path and an actual
degree-budget subset of size floor(n/2). -/
theorem target_max_degree_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hn : 3 ≤ Fintype.card V) (hntree : ¬ G.IsTree)
    (hmax : ∀ v, G.degree v ≤ 2) :
    G.totalDominationNumber ≤ G.annihilationNumber + 1 := by
  classical
  have hconncard := hG.card_vert_le_card_edgeSet_add_one
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card] at hconncard
  have hneq : G.edgeFinset.card + 1 ≠ Fintype.card V := by
    intro heq
    apply hntree
    apply (SimpleGraph.isTree_iff_connected_and_card (G := G)).mpr
    refine ⟨hG, ?_⟩
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using heq
  have hm : Fintype.card V ≤ G.edgeFinset.card := by omega
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel _
  have hTmax : ∀ v, T.degree v ≤ 2 := by
    intro v
    exact (T.degree_le_of_le (v := v) hTG).trans (hmax v)
  have hTl := leaves_tree_max_two T hT (by omega) hTmax
  have hTb := tree_total_domination_bound T hT hn
  rw [hTl] at hTb
  have hmono := total_domination_mono_connected G T hTG hT.connected (by omega)
  have hhalf : Fintype.card V / 2 ≤ (univ : Finset V).card := by simp; omega
  obtain ⟨A, _, hAc⟩ := exists_subset_card_eq hhalf
  have hAb : ∑ v ∈ A, G.degree v ≤ G.edgeFinset.card := by
    calc
      _ ≤ ∑ _v ∈ A, (2 : ℕ) := sum_le_sum (fun v _ => hmax v)
      _ = 2 * A.card := by simp [Nat.mul_comm]
      _ ≤ G.edgeFinset.card := by rw [hAc]; omega
  have hA := card_le_annihilationNumber G A hAb
  rw [hAc] at hA
  omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.target_max_degree_two
