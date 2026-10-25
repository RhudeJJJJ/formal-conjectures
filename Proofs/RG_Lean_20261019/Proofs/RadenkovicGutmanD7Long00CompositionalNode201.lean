/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode198
import Proofs.RadenkovicGutmanD7Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[69,0],[0,0]],[[0,0],[0,0]],[[769,0],[0,0]],[[0,0],[0,0]],[[4252,0],[0,0]],[[0,0],[0,0]],[[13437,0],[0,0]],[[0,0],[0,0]],[[25548,2],[2,0]],[[0,0],[0,0]],[[29348,37],[37,0]],[[0,0],[0,0]],[[19608,198],[198,0]],[[0,0],[0,0]],[[6779,426],[426,0]],[[0,0],[0,0]],[[795,368],[368,0]],[[0,0],[0,0]],[[-63,105],[105,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
