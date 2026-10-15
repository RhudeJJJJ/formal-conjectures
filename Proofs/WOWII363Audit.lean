/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII363Proof

/-! Independent exact-statement and normalization audit for WOWII 363. -/
namespace WOWII363Audit
open SimpleGraph

def supportVertices {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Set V :=
  {s | ∃ p, G.degree p = 1 ∧ G.Adj s p}

noncomputable def isolateCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := by
  classical
  exact (Finset.univ.filter fun s => s ∈ supportVertices G ∧
    ∀ t ∈ supportVertices G, ¬ G.Adj s t).card

lemma isolateCount_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    isolateCount G = (WOWII363Proof.isolatedSupports G).card := by
  classical
  unfold isolateCount WOWII363Proof.isolatedSupports
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change ((∃ p, G.degree p = 1 ∧ G.Adj s p) ∧
      ∀ t, (∃ p, G.degree p = 1 ∧ G.Adj t p) → ¬ G.Adj s t) ↔
    (s ∈ WOWII363Proof.supports G ∧
      ∀ t ∈ WOWII363Proof.supports G, ¬ G.Adj s t)
  simp only [WOWII363Proof.supports, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The support-isolation predicate is exactly isolation in the induced graph. -/
lemma induced_isolation {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (s : supportVertices G) :
    (∀ t ∈ supportVertices G, ¬ G.Adj s.val t) ↔
      ∀ t : supportVertices G, ¬ (G.induce (supportVertices G)).Adj s t := by
  constructor
  · intro h t; exact h t.val t.property
  · intro h t ht; exact h ⟨t,ht⟩

/-- Negative model control: minimum distance to the two peripheral vertices is 9,
whereas their pairwise distance is 10. -/
theorem distance_normalization :
    WOWII363Proof.distanceTo WOWII363Proof.witness {5,10} 17 = 9 ∧
    WOWII363Proof.witness.dist 5 10 = 10 := by
  constructor
  · unfold WOWII363Proof.distanceTo
    have hb : ({5,10} : Finset (Fin 27)).Nonempty := by decide
    rw [dif_pos hb]
    simp_rw [WOWII363Proof.dist_eq_delta]
    decide +revert
  · rw [WOWII363Proof.dist_eq_delta]; decide

theorem exact_target : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsTree → 2 < Fintype.card V →
    (isolateCount G : ℚ) + WOWII363Proof.positiveBoundaryAverage G / 2 ≤
      G.totalDominationNumber := by
  simpa only [isolateCount_eq] using WOWII363Proof.conjecture363

#print axioms isolateCount_eq
#print axioms induced_isolation
#print axioms distance_normalization
#print axioms exact_target
end WOWII363Audit
