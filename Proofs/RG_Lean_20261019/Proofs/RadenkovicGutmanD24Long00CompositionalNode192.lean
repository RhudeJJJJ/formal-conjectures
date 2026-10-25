/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode191
import Proofs.RadenkovicGutmanD24Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[54,0],[0,0]],[[0,0],[0,0]],[[548,0],[0,0]],[[0,0],[0,0]],[[2894,0],[0,0]],[[0,0],[0,0]],[[8928,0],[0,0]],[[0,0],[0,0]],[[16776,2],[2,0]],[[0,0],[0,0]],[[19172,40],[40,0]],[[0,0],[0,0]],[[12670,236],[236,0]],[[0,0],[0,0]],[[4014,576],[576,0]],[[0,0],[0,0]],[[54,594],[594,0]],[[0,0],[0,0]],[[-216,216],[216,2]],[[0],[0,0]],[[0],[0,24]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
