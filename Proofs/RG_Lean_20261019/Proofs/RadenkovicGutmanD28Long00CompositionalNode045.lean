/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode044
import Proofs.RadenkovicGutmanD28Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,28]],[[0,0],[0,0]],[[-252,252],[252,2]],[[0,0],[0]],[[66,690],[690]],[[0,0],[0]],[[4682,664],[664]],[[0,0],[0]],[[14726,268],[268]],[[0,0],[0]],[[22196,44],[44]],[[0,0],[0]],[[19320,2],[2]],[[0]],[[10204]],[[0]],[[3270]],[[0]],[[608]],[[0]],[[58]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
