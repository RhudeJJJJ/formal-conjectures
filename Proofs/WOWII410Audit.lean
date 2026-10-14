/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII410Proof

namespace WOWII410Audit
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def neighborhood (G : SimpleGraph V) (I : Finset V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ u ∈ I, G.Adj u v

noncomputable def difference (G : SimpleGraph V) (I : Finset V) : ℤ :=
  (I.card : ℤ) - (neighborhood G I).card

def IsCritical (G : SimpleGraph V) (I : Finset V) : Prop :=
  G.IsIndepSet (I : Set V) ∧ ∀ J : Finset V,
    G.IsIndepSet (J : Set V) → difference G J ≤ difference G I

def IsMaximumCritical (G : SimpleGraph V) (I : Finset V) : Prop :=
  IsCritical G I ∧ ∀ J : Finset V, IsCritical G J → J.card ≤ I.card

noncomputable def criticalUnion (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∃ I : Finset V, IsMaximumCritical G I ∧ v ∈ I

def minimumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := univ.filter fun v => ∀ w, G.degree v ≤ G.degree w
def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V := univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def evenCount (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (univ.filter fun w => Even (G.dist v w)).card
noncomputable def evenMax (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, evenCount G w ≤ evenCount G v
noncomputable def evenMin (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => ∀ w, evenCount G v ≤ evenCount G w
def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Finset V) : ℕ := (G.edgeFinset.filter fun e => e.toFinset ⊆ Q).card
def baseBound (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (univ \ minimumVertices G).card + (univ \ maximumVertices G).card


/-- Complete source target with separately rewritten critical-set and extremal definitions. -/
theorem exact410a (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : 2 < Fintype.card V) :
    (criticalUnion G).card ≤ baseBound G + edgesOn G (evenMax G) := by
  exact WOWII410Proof.conjecture410a G hc hn

theorem exact410b (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) (hn : 2 < Fintype.card V) :
    (criticalUnion G).card ≤ baseBound G + edgesOn G (evenMin G) := by
  exact WOWII410Proof.conjecture410b G hc hn

#print axioms CriticalIndependentProof.maximumCritical_exists
#print axioms WOWII410Proof.regular_positive
#print axioms WOWII410Proof.cross_sum
#print axioms WOWII410Proof.regular_critical_saturated
#print axioms WOWII410Proof.critical_partition
#print axioms WOWII410Proof.walk_parity
#print axioms WOWII410Proof.even_constant_of_union
#print axioms WOWII410Proof.positive_extrema_unchanged
#print axioms WOWII410Proof.conjecture410a
#print axioms WOWII410Proof.conjecture410b
#print axioms exact410a
#print axioms exact410b
end WOWII410Audit
