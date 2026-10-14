/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII416Proof

namespace WOWII416Audit
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

noncomputable def leaves (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => G.degree v = 1

noncomputable def doubleNeighborhood (G : SimpleGraph V) : Finset V :=
  neighborhood G (neighborhood G (leaves G))

noncomputable def isolatesOn (G : SimpleGraph V) (Q : Finset V) : Finset V := by
  classical
  exact Q.filter fun v => ∀ w ∈ Q, ¬G.Adj v w


theorem exact_strengthening (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V) (hd : ∀ u v, G.dist u v ≤ 2) :
    (isolatesOn G (doubleNeighborhood G)).card ≤ (criticalUnion G).card := by
  exact WOWII416Proof.strengthened416 G hc hn hd

theorem exact416 (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < Fintype.card V) (hd : ∀ u v, G.dist u v ≤ 2) :
    ((isolatesOn G (doubleNeighborhood G)).card : ℤ) - 2 ≤ (criticalUnion G).card := by
  exact WOWII416Proof.conjecture416 G hc hn hd

#print axioms CriticalIndependentProof.maximumCritical_exists
#print axioms CriticalIndependentProof.leaf_mem_union
#print axioms WOWII416Proof.support_universal
#print axioms WOWII416Proof.isolates_subset_leaves
#print axioms WOWII416Proof.strengthened416
#print axioms WOWII416Proof.conjecture416
#print axioms exact_strengthening
#print axioms exact416
end WOWII416Audit
