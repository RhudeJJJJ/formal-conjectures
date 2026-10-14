/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII396Proof

namespace WOWII396Audit
open SimpleGraph

def IsTwoDominating {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) : Prop :=
  ∀ v ∉ D, 2 ≤ (D.filter fun w => G.Adj v w).card

noncomputable def twoDominationNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {n | ∃ D : Finset V, IsTwoDominating G D ∧ D.card = n}

def degreeFrequency {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℕ :=
  (Finset.univ.filter fun v => G.degree v = j).card

def maximumFrequency {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.range (Fintype.card V + 1)).sup (degreeFrequency G)

def degreeModes {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.range (Fintype.card V + 1)).filter fun j => degreeFrequency G j = maximumFrequency G

def boundaryCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : V × V =>
    G.Adj p.1 p.2 ∧ 3 ≤ G.degree p.1 ∧ G.degree p.2 < 3).card

def proposedBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (degreeModes G).card + maximumFrequency G + boundaryCount G

/-- Independent statement and definitions, without importing an upstream placeholder. -/
theorem exact_statement : False ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
        twoDominationNumber G ≤ proposedBound G := by
  exact ⟨False.elim, fun h => WOWII396Proof.conjecture396 h⟩

#print axioms WOWII396Proof.witness_connected
#print axioms WOWII396Proof.modes
#print axioms WOWII396Proof.bound_eq
#print axioms WOWII396Proof.two_per_block
#print axioms WOWII396Proof.total_lower
#print axioms WOWII396Proof.selected_certificate
#print axioms WOWII396Proof.two_domination_eq
#print axioms WOWII396Proof.conjecture396
#print axioms exact_statement
end WOWII396Audit

