/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode197
import Proofs.RadenkovicGutmanD5Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[55,0],[0,0]],[[0,0],[0,0]],[[563,0],[0,0]],[[0,0],[0,0]],[[2988,0],[0,0]],[[0,0],[0,0]],[[9247,0],[0,0]],[[0,0],[0,0]],[[17412,2],[2,0]],[[0,0],[0,0]],[[19948,31],[31,0]],[[0,0],[0,0]],[[13344,154],[154,0]],[[0,0],[0,0]],[[4621,318],[318,0]],[[0,0],[0,0]],[[537,268],[268,0]],[[0,0],[0,0]],[[-45,75],[75,2]],[[0],[0,0]],[[0],[0,5]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
