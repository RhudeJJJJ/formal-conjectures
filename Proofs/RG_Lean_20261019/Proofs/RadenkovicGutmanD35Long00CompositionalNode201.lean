/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode198
import Proofs.RadenkovicGutmanD35Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[209,0],[0,0]],[[0,0],[0,0]],[[2869,0],[0,0]],[[0,0],[0,0]],[[17412,0],[0,0]],[[0,0],[0,0]],[[58097,0],[0,0]],[[0,0],[0,0]],[[114588,2],[2,0]],[[0,0],[0,0]],[[135300,121],[121,0]],[[0,0],[0,0]],[[92464,814],[814,0]],[[0,0],[0,0]],[[32623,1938],[1938,0]],[[0,0],[0,0]],[[3903,1768],[1768,0]],[[0,0],[0,0]],[[-315,525],[525,2]],[[0],[0,0]],[[0],[0,35]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
