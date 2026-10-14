/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII395bProof

namespace WOWII395bAudit
open SimpleGraph
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

def smallestMode {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  WithTop.untopD 0 (degreeModes G).min

def minimumVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = G.minDegree

def remaining {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ \ minimumVertices G

def proposedBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  degreeFrequency G (smallestMode G) +
    (G.induce (remaining G : Set V)).minDegree +
    (Finset.univ.filter fun v => G.degree v < 3).card

/-- The complete edge list is specified separately from the proof's clique constructor. -/
def listedEdges : Finset (Fin 15 × Fin 15) := {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8),(9,10),(9,11),(9,12),(9,13),(9,14),(10,11),(10,12),(10,13),(10,14),(11,12),(11,13),(11,14),(12,13),(12,14),(13,14),(0,4),(4,9),(5,10),(5,11),(6,9),(6,11),(6,12)}
theorem input_matches : ∀ u v, WOWII395bProof.witness.Adj u v ↔
    (u,v) ∈ listedEdges ∨ (v,u) ∈ listedEdges := by decide

theorem exact_statement : False ↔ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 2 < Fintype.card V →
        (remaining G).Nonempty → twoDominationNumber G ≤ proposedBound G := by
  exact ⟨False.elim,fun h => WOWII395bProof.conjecture395b h⟩

#print axioms WOWII395bProof.witness_connected
#print axioms WOWII395bProof.degree_spec
#print axioms WOWII395bProof.modes
#print axioms WOWII395bProof.minimum_degree
#print axioms WOWII395bProof.induced_minimum_degree
#print axioms WOWII395bProof.bound_eq
#print axioms WOWII395bProof.two_per_block
#print axioms WOWII395bProof.two_domination_eq
#print axioms WOWII395bProof.conjecture395b
#print axioms input_matches
#print axioms exact_statement
end WOWII395bAudit
