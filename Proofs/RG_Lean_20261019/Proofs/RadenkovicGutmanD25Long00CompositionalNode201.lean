/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode198
import Proofs.RadenkovicGutmanD25Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[159,0],[0,0]],[[0,0],[0,0]],[[2119,0],[0,0]],[[0,0],[0,0]],[[12712,0],[0,0]],[[0,0],[0,0]],[[42147,0],[0,0]],[[0,0],[0,0]],[[82788,2],[2,0]],[[0,0],[0,0]],[[97460,91],[91,0]],[[0,0],[0,0]],[[66444,594],[594,0]],[[0,0],[0,0]],[[23393,1398],[1398,0]],[[0,0],[0,0]],[[2793,1268],[1268,0]],[[0,0],[0,0]],[[-225,375],[375,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
