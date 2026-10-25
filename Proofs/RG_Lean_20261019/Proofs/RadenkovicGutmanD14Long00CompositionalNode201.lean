/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode198
import Proofs.RadenkovicGutmanD14Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[104,0],[0,0]],[[0,0],[0,0]],[[1294,0],[0,0]],[[0,0],[0,0]],[[7542,0],[0,0]],[[0,0],[0,0]],[[24602,0],[0,0]],[[0,0],[0,0]],[[47808,2],[2,0]],[[0,0],[0,0]],[[55836,58],[58,0]],[[0,0],[0,0]],[[37822,352],[352,0]],[[0,0],[0,0]],[[13240,804],[804,0]],[[0,0],[0,0]],[[1572,718],[718,0]],[[0,0],[0,0]],[[-126,210],[210,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
