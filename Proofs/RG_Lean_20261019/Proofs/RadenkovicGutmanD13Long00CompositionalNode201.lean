/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode198
import Proofs.RadenkovicGutmanD13Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[99,0],[0,0]],[[0,0],[0,0]],[[1219,0],[0,0]],[[0,0],[0,0]],[[7072,0],[0,0]],[[0,0],[0,0]],[[23007,0],[0,0]],[[0,0],[0,0]],[[44628,2],[2,0]],[[0,0],[0,0]],[[52052,55],[55,0]],[[0,0],[0,0]],[[35220,330],[330,0]],[[0,0],[0,0]],[[12317,750],[750,0]],[[0,0],[0,0]],[[1461,668],[668,0]],[[0,0],[0,0]],[[-117,195],[195,2]],[[0],[0,0]],[[0],[0,13]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
