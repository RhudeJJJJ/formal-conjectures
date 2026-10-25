/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode198
import Proofs.RadenkovicGutmanD31Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[189,0],[0,0]],[[0,0],[0,0]],[[2569,0],[0,0]],[[0,0],[0,0]],[[15532,0],[0,0]],[[0,0],[0,0]],[[51717,0],[0,0]],[[0,0],[0,0]],[[101868,2],[2,0]],[[0,0],[0,0]],[[120164,109],[109,0]],[[0,0],[0,0]],[[82056,726],[726,0]],[[0,0],[0,0]],[[28931,1722],[1722,0]],[[0,0],[0,0]],[[3459,1568],[1568,0]],[[0,0],[0,0]],[[-279,465],[465,2]],[[0],[0,0]],[[0],[0,31]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
