/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode197
import Proofs.RadenkovicGutmanD35Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[205,0],[0,0]],[[0,0],[0,0]],[[2813,0],[0,0]],[[0,0],[0,0]],[[17088,0],[0,0]],[[0,0],[0,0]],[[57097,0],[0,0]],[[0,0],[0,0]],[[112812,2],[2,0]],[[0,0],[0,0]],[[133468,121],[121,0]],[[0,0],[0,0]],[[91404,814],[814,0]],[[0,0],[0,0]],[[32311,1938],[1938,0]],[[0,0],[0,0]],[[3867,1768],[1768,0]],[[0,0],[0,0]],[[-315,525],[525,2]],[[0],[0,0]],[[0],[0,35]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
