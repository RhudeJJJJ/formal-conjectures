/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII423Proof

open SimpleGraph Finset
namespace WOWII423Audit

/-- Independently written source type, without the proof's neighborhood abbreviation. -/
theorem original_statement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (hn : 3 < Fintype.card V) :
    let A := Finset.univ.filter fun v => G.degree v = G.minDegree
    let M := Finset.univ.filter fun v => G.degree v = G.maxDegree
    let N := Finset.univ.filter fun v => v ∈ A ∨ ∃ a ∈ A, G.Adj a v
    G.indepDominationNumber ≤ (G.internalEdges M).card +
      (G.induce (N : Set V)).indepNum *
      (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum := by
  classical
  have h := WOWII423Proof.conjecture423 G hG hn
  dsimp only at h ⊢
  have hN : WOWII423Proof.closedNeighborhood G
      (Finset.univ.filter fun v => G.degree v = G.minDegree) =
      Finset.univ.filter (fun v =>
        v ∈ (Finset.univ.filter fun w => G.degree w = G.minDegree) ∨
        ∃ a ∈ (Finset.univ.filter fun w => G.degree w = G.minDegree), G.Adj a v) := by
    ext v
    simp [WOWII423Proof.closedNeighborhood]
  rw [hN] at h
  convert h using 1
  congr 4 <;> ext v <;> simp

/-- Independently written cut type, including the original subtract-one form. -/
theorem cut_statement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) {a b : V}
    (ha : a ∈ A) (hb : b ∉ A) (hab : G.Adj a b) :
    let N := Finset.univ.filter fun v => v ∈ A ∨ ∃ a ∈ A, G.Adj a v
    G.indepDominationNumber ≤ (G.induce (N : Set V)).indepNum +
      (G.induce ((Finset.univ \ A : Finset V) : Set V)).indepNum - 1 := by
  have h := WOWII423Proof.cut_bound G A ha hb hab
  classical
  have hN : WOWII423Proof.closedNeighborhood G A =
      Finset.univ.filter (fun v => v ∈ A ∨ ∃ a ∈ A, G.Adj a v) := by
    ext v
    simp [WOWII423Proof.closedNeighborhood]
  rw [hN] at h
  dsimp only
  omega

#print axioms WOWII423Proof.cut_bound
#print axioms WOWII423Proof.product_cut_bound
#print axioms WOWII423Proof.conjecture423
#print axioms original_statement
#print axioms cut_statement

end WOWII423Audit
