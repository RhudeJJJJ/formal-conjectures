/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode198
import Proofs.RadenkovicGutmanD6Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[64,0],[0,0]],[[0,0],[0,0]],[[694,0],[0,0]],[[0,0],[0,0]],[[3782,0],[0,0]],[[0,0],[0,0]],[[11842,0],[0,0]],[[0,0],[0,0]],[[22368,2],[2,0]],[[0,0],[0,0]],[[25564,34],[34,0]],[[0,0],[0,0]],[[17006,176],[176,0]],[[0,0],[0,0]],[[5856,372],[372,0]],[[0,0],[0,0]],[[684,318],[318,0]],[[0,0],[0,0]],[[-54,90],[90,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
