/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode191
import Proofs.RadenkovicGutmanD8Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[38,0],[0,0]],[[0,0],[0,0]],[[308,0],[0,0]],[[0,0],[0,0]],[[1390,0],[0,0]],[[0,0],[0,0]],[[3824,0],[0,0]],[[0,0],[0,0]],[[6600,2],[2,0]],[[0,0],[0,0]],[[7076,24],[24,0]],[[0,0],[0,0]],[[4446,108],[108,0]],[[0,0],[0,0]],[[1342,224],[224,0]],[[0,0],[0,0]],[[6,210],[210,0]],[[0,0],[0,0]],[[-72,72],[72,2]],[[0],[0,0]],[[0],[0,8]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
