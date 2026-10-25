/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode198
import Proofs.RadenkovicGutmanD45Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[259,0],[0,0]],[[0,0],[0,0]],[[3619,0],[0,0]],[[0,0],[0,0]],[[22112,0],[0,0]],[[0,0],[0,0]],[[74047,0],[0,0]],[[0,0],[0,0]],[[146388,2],[2,0]],[[0,0],[0,0]],[[173140,151],[151,0]],[[0,0],[0,0]],[[118484,1034],[1034,0]],[[0,0],[0,0]],[[41853,2478],[2478,0]],[[0,0],[0,0]],[[5013,2268],[2268,0]],[[0,0],[0,0]],[[-405,675],[675,2]],[[0],[0,0]],[[0],[0,45]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
