/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII422dProof

/-! Audit of the source-conditioned 422d-U reading. -/
namespace WOWII422dAudit
open SimpleGraph Finset

lemma containment_is_nonproper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ WOWII422dProof.containingVertices G ↔
      ∃ u, u ≠ v ∧ insert u (G.neighborSet u) ⊆ insert v (G.neighborSet v) := by
  simp only [WOWII422dProof.containingVertices, mem_filter, mem_univ, true_and,
    Set.subset_def, Set.mem_insert_iff, SimpleGraph.mem_neighborSet]

def properVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ u, u ≠ v ∧
    insert u (G.neighborFinset u) ⊂ insert v (G.neighborFinset v)

/-- The same graph has no properly containing vertex. Thus the certificate
cannot accidentally refute the different strict-containment statement. -/
theorem strict_control : properVertices WOWII422dProof.witness = ∅ := by decide

theorem damaged_controls :
    ¬WOWII422dProof.witness.IsIndepDominating
      (({0,1,4,10} : Finset (Fin 12)) : Set (Fin 12)) ∧
    ¬WOWII422dProof.witness.IsDominating
      (({0,1,8} : Finset (Fin 12)) : Set (Fin 12)) := by
  change ¬((∀ u ∈ ({0,1,4,10} : Finset (Fin 12)), ∀ v ∈ ({0,1,4,10} : Finset (Fin 12)),
    u ≠ v → ¬WOWII422dProof.witness.Adj u v) ∧
    (∀ v, v ∈ ({0,1,4,10} : Finset (Fin 12)) ∨ ∃ w ∈ ({0,1,4,10} : Finset (Fin 12)),
      WOWII422dProof.witness.Adj v w)) ∧
    ¬(∀ v, v ∈ ({0,1,8} : Finset (Fin 12)) ∨ ∃ w ∈ ({0,1,8} : Finset (Fin 12)),
      WOWII422dProof.witness.Adj v w)
  decide

theorem exact_target : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card V →
      G.indepDominationNumber ≤ WOWII422dProof.bound G :=
  WOWII422dProof.conjecture422d_upper

#print axioms containment_is_nonproper
#print axioms strict_control
#print axioms damaged_controls
#print axioms exact_target
end WOWII422dAudit
