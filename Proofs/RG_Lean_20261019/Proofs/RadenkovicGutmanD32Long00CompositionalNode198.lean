/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode197
import Proofs.RadenkovicGutmanD32Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[190,0],[0,0]],[[0,0],[0,0]],[[2588,0],[0,0]],[[0,0],[0,0]],[[15678,0],[0,0]],[[0,0],[0,0]],[[52312,0],[0,0]],[[0,0],[0,0]],[[103272,2],[2,0]],[[0,0],[0,0]],[[122116,112],[112,0]],[[0,0],[0,0]],[[83598,748],[748,0]],[[0,0],[0,0]],[[29542,1776],[1776,0]],[[0,0],[0,0]],[[3534,1618],[1618,0]],[[0,0],[0,0]],[[-288,480],[480,2]],[[0],[0,0]],[[0],[0,32]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
