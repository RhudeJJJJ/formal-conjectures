/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode198
import Proofs.RadenkovicGutmanD12Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[94,0],[0,0]],[[0,0],[0,0]],[[1144,0],[0,0]],[[0,0],[0,0]],[[6602,0],[0,0]],[[0,0],[0,0]],[[21412,0],[0,0]],[[0,0],[0,0]],[[41448,2],[2,0]],[[0,0],[0,0]],[[48268,52],[52,0]],[[0,0],[0,0]],[[32618,308],[308,0]],[[0,0],[0,0]],[[11394,696],[696,0]],[[0,0],[0,0]],[[1350,618],[618,0]],[[0,0],[0,0]],[[-108,180],[180,2]],[[0],[0,0]],[[0],[0,12]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
