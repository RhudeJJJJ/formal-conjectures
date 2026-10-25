/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode198
import Proofs.RadenkovicGutmanD21Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[139,0],[0,0]],[[0,0],[0,0]],[[1819,0],[0,0]],[[0,0],[0,0]],[[10832,0],[0,0]],[[0,0],[0,0]],[[35767,0],[0,0]],[[0,0],[0,0]],[[70068,2],[2,0]],[[0,0],[0,0]],[[82324,79],[79,0]],[[0,0],[0,0]],[[56036,506],[506,0]],[[0,0],[0,0]],[[19701,1182],[1182,0]],[[0,0],[0,0]],[[2349,1068],[1068,0]],[[0,0],[0,0]],[[-189,315],[315,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
