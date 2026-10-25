/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode191
import Proofs.RadenkovicGutmanD28Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[58,0],[0,0]],[[0,0],[0,0]],[[608,0],[0,0]],[[0,0],[0,0]],[[3270,0],[0,0]],[[0,0],[0,0]],[[10204,0],[0,0]],[[0,0],[0,0]],[[19320,2],[2,0]],[[0,0],[0,0]],[[22196,44],[44,0]],[[0,0],[0,0]],[[14726,268],[268,0]],[[0,0],[0,0]],[[4682,664],[664,0]],[[0,0],[0,0]],[[66,690],[690,0]],[[0,0],[0,0]],[[-252,252],[252,2]],[[0],[0,0]],[[0],[0,28]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
