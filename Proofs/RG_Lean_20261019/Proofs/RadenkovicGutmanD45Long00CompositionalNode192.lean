/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode191
import Proofs.RadenkovicGutmanD45Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[75,0],[0,0]],[[0,0],[0,0]],[[863,0],[0,0]],[[0,0],[0,0]],[[4868,0],[0,0]],[[0,0],[0,0]],[[15627,0],[0,0]],[[0,0],[0,0]],[[30132,2],[2,0]],[[0,0],[0,0]],[[35048,61],[61,0]],[[0,0],[0,0]],[[23464,404],[404,0]],[[0,0],[0,0]],[[7521,1038],[1038,0]],[[0,0],[0,0]],[[117,1098],[1098,0]],[[0,0],[0,0]],[[-405,405],[405,2]],[[0],[0,0]],[[0],[0,45]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
