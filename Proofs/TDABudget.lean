import Mathlib.Tactic
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.AnnihilationNumber
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination

/-! Exact degree-budget witnesses for the total-domination--annihilation target.
The annihilation number below is the repository's multiset definition.
No equivalence with its separate sorted-prefix definition is assumed. -/

namespace TotalDominationAnnihilationProof
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A degree-budget vertex set gives an annihilation-number lower bound. -/
theorem card_le_annihilationNumber (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : ∑ v ∈ S, G.degree v ≤ G.edgeFinset.card) :
    S.card ≤ G.annihilationNumber := by
  have hm : S.val.map G.degree ≤ G.degreeMultiset := by
    exact Multiset.map_le_map (Finset.val_le_iff.mpr (subset_univ S))
  have hmem : S.val.map G.degree ∈
      (Finset.Iic G.degreeMultiset).filter (fun M => M.sum ≤ G.edgeFinset.card) := by
    simp only [mem_filter, mem_Iic]
    exact ⟨hm, by simpa using hS⟩
  have h := Finset.le_sup (f := Multiset.card) hmem
  simpa [SimpleGraph.annihilationNumber] using h

/-- A total dominating set gives the actual infimum-defined upper bound. -/
theorem totalDominationNumber_le_card (G : SimpleGraph V) (D : Finset V)
    (hD : G.IsTotalDominating (D : Set V)) : G.totalDominationNumber ≤ D.card := by
  exact Nat.sInf_le ⟨D, ⟨hD, rfl⟩⟩

/-- A total dominating set and a degree-budget set close the exact target. -/
theorem target_of_witnesses (G : SimpleGraph V) [DecidableRel G.Adj]
    (D A : Finset V) (hD : G.IsTotalDominating (D : Set V))
    (hA : ∑ v ∈ A, G.degree v ≤ G.edgeFinset.card) (hcard : D.card ≤ A.card + 1) :
    G.totalDominationNumber ≤ G.annihilationNumber + 1 := by
  have hd := totalDominationNumber_le_card G D hD
  have ha := card_le_annihilationNumber G A hA
  omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.card_le_annihilationNumber
#print axioms TotalDominationAnnihilationProof.target_of_witnesses
