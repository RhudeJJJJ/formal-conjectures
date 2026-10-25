import Proofs.GraphicalBell.Universal
import Proofs.GraphicalBell.OriginalBridge

namespace PHOEG.GraphicalBell
open GraphicalBellProof SimpleGraph

/-- The exact submitted coefficientwise statement. The proof also covers empty order. -/
theorem full_coefficientwise {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hn : 1 ≤ Fintype.card V) (k : ℕ) :
    stirling (quasiComplete (Fintype.card V) G.edgeFinset.card) k ≤ stirling G k := by
  have h := model_le_count G (Finset.univ : Finset V) k
  rw [Finset.card_univ, sizeOn_univ, original_model, ← original_stirling_eq_count] at h
  exact_mod_cast h

/-- The exact submitted Bell statement, obtained by summing the proved coefficientwise bound. -/
theorem full_conjecture {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 1 ≤ Fintype.card V) :
    bell (quasiComplete (Fintype.card V) G.edgeFinset.card) ≤ bell G := by
  exact bell_of_coefficientwise (@full_coefficientwise) G hn

end PHOEG.GraphicalBell
