/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode198
import Proofs.RadenkovicGutmanD9Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[79,0],[0,0]],[[0,0],[0,0]],[[919,0],[0,0]],[[0,0],[0,0]],[[5192,0],[0,0]],[[0,0],[0,0]],[[16627,0],[0,0]],[[0,0],[0,0]],[[31908,2],[2,0]],[[0,0],[0,0]],[[36916,43],[43,0]],[[0,0],[0,0]],[[24812,242],[242,0]],[[0,0],[0,0]],[[8625,534],[534,0]],[[0,0],[0,0]],[[1017,468],[468,0]],[[0,0],[0,0]],[[-81,135],[135,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
