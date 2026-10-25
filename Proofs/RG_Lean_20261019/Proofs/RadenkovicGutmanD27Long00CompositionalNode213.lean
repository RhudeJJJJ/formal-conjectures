/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode030
import Proofs.RadenkovicGutmanD27Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[27],[0]],[[0,0],[0]],[[405,0],[0,0]],[[0,0],[0,0]],[[2538,0],[0,0]],[[0,0],[0,0]],[[8613,0],[0,0]],[[0,0],[0,0]],[[17172,0],[0,0]],[[0,0],[0,0]],[[20412,27],[27,0]],[[0,0],[0,0]],[[13878,216],[216,0]],[[0,0],[0,0]],[[4509,594],[594,0]],[[0,0],[0,0]],[[81,648],[648,0]],[[0,0],[0,0]],[[-243,243],[243,0]],[[0],[0,0]],[[0],[0,27]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
