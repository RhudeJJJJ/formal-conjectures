/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReducedReserveAcceptance
import Proofs.RadenkovicGutmanEscapeReducedReserveEvaluation

/-!
# Complete original escape reserve box

The original polynomial, degree vector, Hybrid acceptance, full unit-box nonnegativity and exact evaluation identity retain their original qualified names and types.

Source: [original escape reserve polynomial and statements](https://github.com/RhudeJJJJ/formal-conjectures/blob/4ab5802ec7da33fcb4a54633e2e7c9863c974244/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanEscapeReducedReserve.lean).
-/

namespace Gebendorfer.RadenkovicGutman.EscapeReducedReserve
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem unit_box_nonneg (v : Fin 4 → ℝ) (hv : ∀ i, v i ∈ Icc (0 : ℝ) 1) :
    0 ≤ NestedHorner.eval (NestedInteger.castPoly 4 data) v :=
  NestedIntegerHybrid.accepts_sound 4 degrees data accepted v hv

#print axioms accepted
#print axioms unit_box_nonneg
#print axioms data_eval
end
end Gebendorfer.RadenkovicGutman.EscapeReducedReserve
