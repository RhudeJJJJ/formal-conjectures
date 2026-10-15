import Proofs.WOWII433Proof

/-! Definition and construction audit for the explicit upper/M reading 433-M.
The constructor matches the cyclic translates in the supplied manuscript. -/
namespace WOWII433Audit
open WOWII433Proof SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def incidence (p o : ℕ) : Prop := p < 13 ∧ 13 ≤ o ∧
  (p = ((o - 13) / 3) % 13 ∨ p = ((o - 13) / 3 + 1) % 13 ∨
   p = ((o - 13) / 3 + 3) % 13 ∨ p = ((o - 13) / 3 + 9) % 13 ∨ (p = 0 ∧ o = 16))

def constructedAdj (u v : Fin 52) : Prop := u ≠ v ∧
  ((u.val < 13 ∧ v.val < 13) ∨ incidence u.val v.val ∨ incidence v.val u.val)

lemma construction_matches : ∀ u v : Fin 52, witness.Adj u v ↔ constructedAdj u v := by
  unfold constructedAdj incidence
  decide

/-- Open neighborhood count differs from the closed-neighborhood count. -/
lemma closed_neighborhood_card :
    ((maximumVertices witness) ∪ neighbors witness (maximumVertices witness)).card = 26 := by
  rw [maximum_eq]
  decide

lemma singleton_not_dominating : ¬ witness.IsDominating ({0} : Set (Fin 52)) := by
  simp only [SimpleGraph.IsDominating, Set.mem_singleton_iff]
  decide

lemma added_edge_breaks_independence : ¬ witness.IsIndepSet ({0,16} : Set (Fin 52)) := by
  intro h
  exact h (by simp) (by simp) (by decide) (show witness.Adj 0 16 by decide)

#print axioms construction_matches
#print axioms closed_neighborhood_card
#print axioms added_edge_breaks_independence
end WOWII433Audit
