/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII360Proof

namespace WOWII360Audit
open SimpleGraph

noncomputable def centers {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w,
    Finset.univ.sup (fun x => G.dist v x) ≤ Finset.univ.sup (fun x => G.dist w x)

noncomputable def positiveCenterAverage {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℚ :=
  (∑ u ∈ centers G, ∑ v : V, G.dist u v : ℕ) /
    (((centers G).card * (Fintype.card V - 1) : ℕ) : ℚ)

def leafSupportVertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Set V :=
  {v | G.degree v = 1 ∨ ∃ w, G.degree w = 1 ∧ G.Adj v w}

/-- Exact independent statement of the explicit half-average version. -/
theorem exact_statement : False ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      (Nat.card (G.induce (leafSupportVertices G)).ConnectedComponent : ℚ) +
        positiveCenterAverage G / 2 ≤ G.totalDominationNumber := by
  exact ⟨False.elim, fun h => WOWII360Proof.conjecture360 h⟩

#print axioms WOWII360Proof.dist_eq_delta
#print axioms WOWII360Proof.witness_tree
#print axioms WOWII360Proof.center_spec
#print axioms WOWII360Proof.average_eq
#print axioms WOWII360Proof.active_spec
#print axioms WOWII360Proof.reachable_label
#print axioms WOWII360Proof.component_lower
#print axioms WOWII360Proof.total_bound
#print axioms WOWII360Proof.conjecture360
#print axioms exact_statement
end WOWII360Audit

