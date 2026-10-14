/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII373Proof

namespace WOWII373Audit
open SimpleGraph

noncomputable def periphery {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w,
    Finset.univ.sup (fun x => G.dist w x) ≤ Finset.univ.sup (fun x => G.dist v x)

noncomputable def positivePeripheralAverage {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℚ :=
  (∑ u ∈ periphery G, ∑ v : V, G.dist u v : ℕ) /
    (((periphery G).card * (Fintype.card V - 1) : ℕ) : ℚ)

/-- Independent definitions and exact universal statement, without an upstream placeholder. -/
theorem exact_statement : False ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsTree → 2 < Fintype.card V →
        (2 / 3 : ℚ) * positivePeripheralAverage G ≤ G.totalDominationNumber := by
  exact ⟨False.elim, fun h => WOWII373Proof.conjecture373 h⟩

#print axioms WOWII373Proof.dist_eq_delta
#print axioms WOWII373Proof.witness_tree
#print axioms WOWII373Proof.eccentricity_spec
#print axioms WOWII373Proof.periphery_spec
#print axioms WOWII373Proof.average_eq
#print axioms WOWII373Proof.selected_total
#print axioms WOWII373Proof.total_bound
#print axioms WOWII373Proof.conjecture373
#print axioms exact_statement
end WOWII373Audit

