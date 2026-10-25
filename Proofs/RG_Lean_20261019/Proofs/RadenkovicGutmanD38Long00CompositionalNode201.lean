/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode198
import Proofs.RadenkovicGutmanD38Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[224,0],[0,0]],[[0,0],[0,0]],[[3094,0],[0,0]],[[0,0],[0,0]],[[18822,0],[0,0]],[[0,0],[0,0]],[[62882,0],[0,0]],[[0,0],[0,0]],[[124128,2],[2,0]],[[0,0],[0,0]],[[146652,130],[130,0]],[[0,0],[0,0]],[[100270,880],[880,0]],[[0,0],[0,0]],[[35392,2100],[2100,0]],[[0,0],[0,0]],[[4236,1918],[1918,0]],[[0,0],[0,0]],[[-342,570],[570,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
