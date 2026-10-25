/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode065
import Proofs.RadenkovicGutmanD23Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[23],[0]],[[0,0],[0]],[[368,0],[0]],[[0,0],[0]],[[2461,0],[0]],[[0,0],[0]],[[8924,0],[0]],[[0,0],[0]],[[19044,0],[0]],[[0,0],[0]],[[24288,23],[23]],[[0,0],[0]],[[17917,161],[161]],[[0,0],[0]],[[6900,368],[368]],[[0,0],[0]],[[1035,299],[299]],[[0,0],[0]],[[0,69],[69]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
