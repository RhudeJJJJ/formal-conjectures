/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode030
import Proofs.RadenkovicGutmanD17Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[17],[0]],[[0,0],[0]],[[289,0],[0,0]],[[0,0],[0,0]],[[2074,0],[0,0]],[[0,0],[0,0]],[[8177,0],[0,0]],[[0,0],[0,0]],[[19312,0],[0,0]],[[0,0],[0,0]],[[27948,17],[17,0]],[[0,0],[0,0]],[[24310,136],[136,0]],[[0,0],[0,0]],[[11849,374],[374,0]],[[0,0],[0,0]],[[2703,408],[408,0]],[[0,0],[0,0]],[[153,153],[153,0]],[[0],[0,0]],[[0],[0,17]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
