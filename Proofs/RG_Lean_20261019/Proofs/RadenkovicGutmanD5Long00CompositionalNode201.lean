/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode198
import Proofs.RadenkovicGutmanD5Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[59,0],[0,0]],[[0,0],[0,0]],[[619,0],[0,0]],[[0,0],[0,0]],[[3312,0],[0,0]],[[0,0],[0,0]],[[10247,0],[0,0]],[[0,0],[0,0]],[[19188,2],[2,0]],[[0,0],[0,0]],[[21780,31],[31,0]],[[0,0],[0,0]],[[14404,154],[154,0]],[[0,0],[0,0]],[[4933,318],[318,0]],[[0,0],[0,0]],[[573,268],[268,0]],[[0,0],[0,0]],[[-45,75],[75,2]],[[0],[0,0]],[[0],[0,5]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
