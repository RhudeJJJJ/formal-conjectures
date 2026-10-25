/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode198
import Proofs.RadenkovicGutmanD29Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[179,0],[0,0]],[[0,0],[0,0]],[[2419,0],[0,0]],[[0,0],[0,0]],[[14592,0],[0,0]],[[0,0],[0,0]],[[48527,0],[0,0]],[[0,0],[0,0]],[[95508,2],[2,0]],[[0,0],[0,0]],[[112596,103],[103,0]],[[0,0],[0,0]],[[76852,682],[682,0]],[[0,0],[0,0]],[[27085,1614],[1614,0]],[[0,0],[0,0]],[[3237,1468],[1468,0]],[[0,0],[0,0]],[[-261,435],[435,2]],[[0],[0,0]],[[0],[0,29]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
