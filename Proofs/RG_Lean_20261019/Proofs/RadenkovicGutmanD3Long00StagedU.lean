/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode086
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem expression_identity : e086=NestedClassPolynomials.programU 3 4 4 := by rfl
theorem checked : NestedArithmetic.accepts (NestedClassPolynomials.programU 3 4 4) p086=true := by
  unfold NestedArithmetic.accepts
  apply decide_eq_true
  rw [← expression_identity]
  exact h086
#print axioms expression_identity
#print axioms checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
