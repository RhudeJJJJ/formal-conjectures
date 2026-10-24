/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e120 : NestedArithmetic.Expr 3 := .pow e000 0
noncomputable def p120 : NestedHorner.Poly 3 := [[[1]]]
theorem step120 : p120=NestedArithmetic.power p000 0 := by decide +kernel
#print axioms step120
theorem h120 : NestedArithmetic.compile e120=p120 := StagedExprCompile.compile_pow 0 e120 e000 p000 p120 rfl h000 step120
#print axioms h120
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
