import Proofs.WOWII317Proof

open SimpleGraph

-- Identical hypotheses and conclusion to PR #7225.
theorem wowii317_exact_statement {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (h : (Gᶜ).edgeFinset.card ≤ G.largestInducedTreeSize) :
    IsWellTotallyDominated G :=
  WOWII317Proof.conjecture317 G hG h

#print axioms WOWII317Proof.conjecture317
#print axioms WOWII317Proof.minimal_total_domination_card_two
#print axioms wowii317_exact_statement
