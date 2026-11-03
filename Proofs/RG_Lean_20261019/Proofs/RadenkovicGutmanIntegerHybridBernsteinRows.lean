/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedIntegerHybrid

/-!
# Hybrid acceptance from Bernstein coefficient rows

Exact outer coefficient rows and their lower-dimensional Hybrid certificates imply the unchanged boolean acceptance test.

Source: [original escape reserve polynomial and statements](https://github.com/RhudeJJJJ/formal-conjectures/blob/4ab5802ec7da33fcb4a54633e2e7c9863c974244/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanEscapeReducedReserve.lean).
-/

namespace Gebendorfer.RadenkovicGutman.IntegerHybridBernsteinRows
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- Exact coefficient identities and lower-dimensional Hybrid acceptance
imply the original Hybrid acceptance test at the next dimension. -/
theorem checked {n : ℕ} (d : Fin (n+1) → ℕ) (p : NestedInteger.Poly (n+1))
    (rows : Fin (d 0+1) → NestedInteger.Poly n)
    (hp : p.length ≤ d 0+1)
    (hr : ∀ j, rows j = NestedInteger.coefficientFrom (d 0) j.val 0 p)
    (hs : ∀ j, NestedIntegerHybrid.accepts n (fun i => d i.succ) (rows j) = true) :
    NestedIntegerHybrid.accepts (n+1) d p = true := by
  change (NestedInteger.powerCheck (n+1) p || decide (p.length ≤ d 0+1 ∧
    ∀ j : Fin (d 0+1), NestedIntegerHybrid.accepts n (fun i => d i.succ)
      (NestedInteger.coefficientFrom (d 0) j.val 0 p) = true)) = true
  rw [Bool.or_eq_true]
  right
  apply decide_eq_true
  refine ⟨hp, ?_⟩
  intro j
  rw [← hr j]
  exact hs j

#print axioms checked
end
end Gebendorfer.RadenkovicGutman.IntegerHybridBernsteinRows
