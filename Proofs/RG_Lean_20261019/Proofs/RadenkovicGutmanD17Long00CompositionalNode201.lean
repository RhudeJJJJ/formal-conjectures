/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode198
import Proofs.RadenkovicGutmanD17Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[119,0],[0,0]],[[0,0],[0,0]],[[1519,0],[0,0]],[[0,0],[0,0]],[[8952,0],[0,0]],[[0,0],[0,0]],[[29387,0],[0,0]],[[0,0],[0,0]],[[57348,2],[2,0]],[[0,0],[0,0]],[[67188,67],[67,0]],[[0,0],[0,0]],[[45628,418],[418,0]],[[0,0],[0,0]],[[16009,966],[966,0]],[[0,0],[0,0]],[[1905,868],[868,0]],[[0,0],[0,0]],[[-153,255],[255,2]],[[0],[0,0]],[[0],[0,17]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
