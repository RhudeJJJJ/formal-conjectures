/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode086
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
theorem expression_identity : e086=NestedClassPolynomials.programU 3 4 4 := by rfl
theorem checked : NestedArithmetic.accepts (NestedClassPolynomials.programU 3 4 4) p086=true := 
  StagedExprCompile.accepts_of_identity e086 (NestedClassPolynomials.programU 3 4 4) p086 expression_identity h086
#print axioms expression_identity
#print axioms checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
