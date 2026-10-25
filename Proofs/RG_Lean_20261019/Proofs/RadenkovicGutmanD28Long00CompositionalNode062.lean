/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode044
import Proofs.RadenkovicGutmanD28Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,28]],[[0,0],[0,0]],[[252,252],[252,2]],[[0,0],[0]],[[4470,690],[690]],[[0,0],[0]],[[19834,664],[664]],[[0,0],[0]],[[41434,268],[268]],[[0,0],[0]],[[48892,44],[44]],[[0,0],[0]],[[35096,2],[2]],[[0]],[[15740]],[[0]],[[4378]],[[0]],[[720]],[[0]],[[62]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
