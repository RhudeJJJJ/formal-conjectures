/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode192
import Proofs.RadenkovicGutmanD8Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[38,0],[0,0]],[[0,0],[0,0]],[[308,0],[0,0]],[[0,0],[0,0]],[[1390,0],[0,0]],[[0,0],[0,0]],[[3824,0],[0,0]],[[0,0],[0,0]],[[6600,2],[2,0]],[[0,0],[0,0]],[[7076,24],[24,0]],[[0,0],[0,0]],[[4446,108],[108,0]],[[0,0],[0,0]],[[1342,224],[224,0]],[[0,0],[0,0]],[[6,210],[210,0]],[[0,0],[0,0]],[[-72,72],[72,2]],[[0],[0,0]],[[0],[0,8]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
