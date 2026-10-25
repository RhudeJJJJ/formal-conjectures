/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode044
import Proofs.RadenkovicGutmanD45Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,45]],[[0,0],[0,0]],[[-405,405],[405,2]],[[0,0],[0]],[[117,1098],[1098]],[[0,0],[0]],[[7521,1038],[1038]],[[0,0],[0]],[[23464,404],[404]],[[0,0],[0]],[[35048,61],[61]],[[0,0],[0]],[[30132,2],[2]],[[0]],[[15627]],[[0]],[[4868]],[[0]],[[863]],[[0]],[[75]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
