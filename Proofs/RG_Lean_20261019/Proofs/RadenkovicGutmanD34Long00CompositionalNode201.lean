/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode198
import Proofs.RadenkovicGutmanD34Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[204,0],[0,0]],[[0,0],[0,0]],[[2794,0],[0,0]],[[0,0],[0,0]],[[16942,0],[0,0]],[[0,0],[0,0]],[[56502,0],[0,0]],[[0,0],[0,0]],[[111408,2],[2,0]],[[0,0],[0,0]],[[131516,118],[118,0]],[[0,0],[0,0]],[[89862,792],[792,0]],[[0,0],[0,0]],[[31700,1884],[1884,0]],[[0,0],[0,0]],[[3792,1718],[1718,0]],[[0,0],[0,0]],[[-306,510],[510,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
