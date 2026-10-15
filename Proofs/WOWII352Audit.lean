/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII352Proof

/-! Exact-target and closed-neighborhood audit for WOWII 352. -/
namespace WOWII352Audit
open SimpleGraph Finset

lemma closed_neighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    v ∈ WOWII352Proof.closedDegreeTwo G ↔
      G.degree v = 2 ∨ v ∈ ⋃ u ∈ {u | G.degree u = 2}, G.neighborSet u := by
  simp only [WOWII352Proof.closedDegreeTwo, mem_filter, mem_univ, true_and,
    Set.mem_iUnion, Set.mem_ofPred_eq, SimpleGraph.mem_neighborSet]
  constructor
  · rintro (h | ⟨u,hu,hvu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u,hu,hvu.symm⟩
  · rintro (h | ⟨u,hu,huv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u,hu,huv.symm⟩

theorem separator_control :
    (5 : Fin 18) ∉ WOWII352Proof.closedDegreeTwo WOWII352Proof.witness ∧
    (4 : Fin 18) ∈ WOWII352Proof.closedDegreeTwo WOWII352Proof.witness ∧
    WOWII352Proof.closedDegreeTwo WOWII352Proof.witness = {0,1,2,3,4,6,7,8,9,10,11} := by
  decide

theorem exact_target : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      Nat.card (G.induce (WOWII352Proof.closedDegreeTwo G : Set V)).ConnectedComponent +
        ⌈WOWII352Proof.averageMaxEccentricity G / 2⌉₊ ≤ G.totalDominationNumber :=
  WOWII352Proof.conjecture352

#print axioms closed_neighborhood
#print axioms separator_control
#print axioms exact_target
end WOWII352Audit
