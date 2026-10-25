/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode198
import Proofs.RadenkovicGutmanD8Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[74,0],[0,0]],[[0,0],[0,0]],[[844,0],[0,0]],[[0,0],[0,0]],[[4722,0],[0,0]],[[0,0],[0,0]],[[15032,0],[0,0]],[[0,0],[0,0]],[[28728,2],[2,0]],[[0,0],[0,0]],[[33132,40],[40,0]],[[0,0],[0,0]],[[22210,220],[220,0]],[[0,0],[0,0]],[[7702,480],[480,0]],[[0,0],[0,0]],[[906,418],[418,0]],[[0,0],[0,0]],[[-72,120],[120,2]],[[0],[0,0]],[[0],[0,8]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
