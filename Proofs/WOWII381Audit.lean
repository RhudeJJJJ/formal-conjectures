/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.WOWII381Proof

/-! Definition audit and boundary controls for WOWII 381. -/
namespace WOWII381Audit
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Isolation is in the induced graph, while degree in the denominator is ambient. -/
lemma induced_isolation (S : Finset V) (v : V) (hv : v ∈ S) :
    (∀ w ∈ S, ¬ G.Adj v w) ↔
    ∀ w : (S : Set V), ¬ (G.induce (S : Set V)).Adj ⟨v,hv⟩ w := by
  constructor
  · intro h w; exact h w.val w.property
  · intro h w hw; exact h ⟨w,hw⟩

omit [DecidableEq V] in
/-- The open neighborhood is the union of the ambient neighbor sets of all supports. -/
lemma neighborhood_union (v : V) :
    v ∈ WOWII381Proof.neighbors G (WOWII381Proof.supports G) ↔
    v ∈ ⋃ s ∈ (WOWII381Proof.supports G : Set V), G.neighborSet s := by
  simp only [WOWII381Proof.mem_neighbors, Set.mem_iUnion, mem_coe,
    SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨s,hs,hvs⟩; exact ⟨s,hs,hvs.symm⟩
  · rintro ⟨s,hs,hsv⟩; exact ⟨s,hs,hsv.symm⟩

/-- P4 is a control where N(S) meets S; no supports are deleted from N(S). -/
def pathFour : SimpleGraph (Fin 4) where
  Adj v w := v.val + 1 = w.val ∨ w.val + 1 = v.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩
instance : DecidableRel pathFour.Adj := inferInstanceAs
  (DecidableRel fun v w : Fin 4 => v.val + 1 = w.val ∨ w.val + 1 = v.val)

theorem open_neighborhood_control :
    WOWII381Proof.supports pathFour = {1,2} ∧
    WOWII381Proof.neighbors pathFour (WOWII381Proof.supports pathFour) = univ ∧
    WOWII381Proof.isolates pathFour (WOWII381Proof.neighbors pathFour
      (WOWII381Proof.supports pathFour)) = ∅ ∧
    WOWII381Proof.supportDegree pathFour = 2 := by decide

/-- Exact target of the original tree conjecture. -/
theorem exact_target : ∀ (W : Type) [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → 2 < Fintype.card W →
    ((WOWII381Proof.isolates T (WOWII381Proof.neighbors T
      (WOWII381Proof.supports T))).card : ℚ) /
      ((WOWII381Proof.supportDegree T : ℚ) - 1) ≤ T.totalDominationNumber := by
  intro W _ _ T _ hT hn
  exact WOWII381Proof.conjecture381_ratio T hT hn

#print axioms induced_isolation
#print axioms neighborhood_union
#print axioms open_neighborhood_control
#print axioms exact_target
end WOWII381Audit
