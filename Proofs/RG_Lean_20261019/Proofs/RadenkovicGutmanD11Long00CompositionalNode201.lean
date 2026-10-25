/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode198
import Proofs.RadenkovicGutmanD11Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[89,0],[0,0]],[[0,0],[0,0]],[[1069,0],[0,0]],[[0,0],[0,0]],[[6132,0],[0,0]],[[0,0],[0,0]],[[19817,0],[0,0]],[[0,0],[0,0]],[[38268,2],[2,0]],[[0,0],[0,0]],[[44484,49],[49,0]],[[0,0],[0,0]],[[30016,286],[286,0]],[[0,0],[0,0]],[[10471,642],[642,0]],[[0,0],[0,0]],[[1239,568],[568,0]],[[0,0],[0,0]],[[-99,165],[165,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
