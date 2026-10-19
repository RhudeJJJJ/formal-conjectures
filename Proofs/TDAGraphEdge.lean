import Proofs.TDAGraphBudget
import Proofs.TDATransfer
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual graph edge deletion and its exact effects on degree budgets. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
theorem degree_restore_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) (x : V) :
    G.degree x = (G.deleteEdges {s(u, v)}).degree x +
      (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
  have hne := huv.ne
  by_cases hxu : x = u
  · subst x
    have hN : (G.deleteEdges {s(u, v)}).neighborFinset u = (G.neighborFinset u).erase v := by
      ext y
      simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff, mem_erase]
      simp only [true_and, hne, false_and, or_false]
      tauto
    have hp := huv.degree_pos_left
    have hdeg : (G.deleteEdges {s(u, v)}).degree u + 1 = G.degree u := by
      change ((G.deleteEdges {s(u, v)}).neighborFinset u).card + 1 = (G.neighborFinset u).card
      rw [hN, card_erase_of_mem ((mem_neighborFinset _ _ _).mpr huv)]
      change G.degree u - 1 + 1 = G.degree u
      omega
    simpa [hne] using hdeg.symm
  · by_cases hxv : x = v
    · subst x
      have hN : (G.deleteEdges {s(u, v)}).neighborFinset v = (G.neighborFinset v).erase u := by
        ext y
        simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff, mem_erase]
        simp only [hne.symm, false_and, false_or, true_and]
        tauto
      have hp := huv.degree_pos_right
      have hdeg : (G.deleteEdges {s(u, v)}).degree v + 1 = G.degree v := by
        change ((G.deleteEdges {s(u, v)}).neighborFinset v).card + 1 = (G.neighborFinset v).card
        rw [hN, card_erase_of_mem ((mem_neighborFinset _ _ _).mpr huv.symm)]
        change G.degree v - 1 + 1 = G.degree v
        omega
      simpa [hne.symm] using hdeg.symm
    · have hN : (G.deleteEdges {s(u, v)}).neighborFinset x = G.neighborFinset x := by
        ext y
        simp [mem_neighborFinset, deleteEdges_adj, hxu, hxv]
      have hdeg : (G.deleteEdges {s(u, v)}).degree x = G.degree x := congrArg Finset.card hN
      simp [hxu, hxv, hdeg]

open scoped Classical in
theorem edge_count_delete_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges {s(u, v)}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have hmem : s(u, v) ∈ G.edgeFinset := by simpa using huv
  have hE : (G.deleteEdges {s(u, v)}).edgeFinset = G.edgeFinset.erase s(u, v) := by
    ext e
    simp [and_comm]
  rw [hE, card_erase_of_mem hmem]
  have hp := card_pos.mpr ⟨s(u, v), hmem⟩
  omega

omit [DecidableEq V] in
theorem total_domination_mono_connected (G H : SimpleGraph V)
    [DecidableRel H.Adj] (hHG : H ≤ G) (hH : H.Connected) (hn : 2 ≤ Fintype.card V) :
    G.totalDominationNumber ≤ H.totalDominationNumber := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hne : {n | ∃ D : Finset V, H.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card V, univ, ?_, card_univ⟩
    intro v
    obtain ⟨w, hvw⟩ := (H.degree_pos_iff_exists_adj v).mp
      (hH.preconnected.degree_pos_of_nontrivial v)
    exact ⟨w, mem_univ _, hvw⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hTD : G.IsTotalDominating (D : Set V) := by
    intro v
    obtain ⟨w, hwD, hvw⟩ := hD.isTotalDominating v
    exact ⟨w, hwD, hHG hvw⟩
  have hle := totalDominationNumber_le_card G D hTD
  rwa [hD.card_eq] at hle

open scoped Classical in
/-- In the low-budget branch, deleting the indicated high-degree cycle endpoint
cannot increase the annihilation number. -/
theorem annihilation_delete_high_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) (hvhigh : 3 ≤ G.degree v)
    (hlarge : G.edgeFinset.card < ∑ x ∈ lowVertices G, G.degree x) :
    (G.deleteEdges {s(u, v)}).annihilationNumber ≤ G.annihilationNumber := by
  have hc := edge_count_delete_edge G huv
  have hm : 0 < G.edgeFinset.card := by omega
  obtain ⟨A, hAc, hAb⟩ := exists_annihilation_set (G.deleteEdges {s(u, v)})
  have hlow : ∀ x ∈ lowVertices G, G.degree x ≤ 2 := by
    intro x hx
    exact (mem_filter.mp hx).2
  have hAb' : ∑ x ∈ A, (G.deleteEdges {s(u, v)}).degree x ≤ G.edgeFinset.card - 1 := by omega
  obtain ⟨B, hBc, hBb⟩ := budget_transfer_edge (fun x => G.degree x)
    (fun x => (G.deleteEdges {s(u, v)}).degree x) G.edgeFinset.card hm u v
    (degree_restore_edge G huv) hvhigh (lowVertices G) A hlow hlarge hAb'
  have hle := card_le_annihilationNumber G B hBb
  rwa [hBc, hAc] at hle

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.degree_restore_edge
#print axioms TotalDominationAnnihilationProof.annihilation_delete_high_edge

