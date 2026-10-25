/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e120 : NestedArithmetic.Expr 3 := .pow e006 2
noncomputable def p120 : NestedHorner.Poly 3 := [[[1]]]
theorem step120 : p120=NestedArithmetic.power p006 2 := by decide +kernel
#print axioms step120
theorem h120 : NestedArithmetic.compile e120=p120 := StagedExprCompile.compile_pow 2 e120 e006 p006 p120 rfl h006 step120
#print axioms h120
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
