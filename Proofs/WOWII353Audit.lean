/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII353Proof

namespace WOWII353Audit
open SimpleGraph

/-- Independently defined largest component order, including order zero for an empty graph. -/
noncomputable def largestComponentOrder {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Finset.univ.sup fun v => Nat.card (G.connectedComponentMk v).supp

/-- Exact proposed statement, without importing an upstream placeholder. -/
theorem exact_statement : False ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      (Nat.card (G.induce {v | G.degree v = 2}).ConnectedComponent : ℚ) +
        (largestComponentOrder (G.induce {v | G.degree v = G.maxDegree}) : ℚ) / 2 ≤
          G.totalDominationNumber := by
  exact ⟨False.elim, fun h => WOWII353Proof.conjecture353 h⟩

#print axioms WOWII353Proof.witness_tree
#print axioms WOWII353Proof.selected_total
#print axioms WOWII353Proof.total_bound
#print axioms WOWII353Proof.degree_two_component_count
#print axioms WOWII353Proof.large_component
#print axioms WOWII353Proof.counterexample
#print axioms WOWII353Proof.conjecture353
#print axioms exact_statement
end WOWII353Audit

