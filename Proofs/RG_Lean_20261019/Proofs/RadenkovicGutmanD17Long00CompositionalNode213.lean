/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode030
import Proofs.RadenkovicGutmanD17Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[17],[0]],[[0,0],[0]],[[255,0],[0,0]],[[0,0],[0,0]],[[1598,0],[0,0]],[[0,0],[0,0]],[[5423,0],[0,0]],[[0,0],[0,0]],[[10812,0],[0,0]],[[0,0],[0,0]],[[12852,17],[17,0]],[[0,0],[0,0]],[[8738,136],[136,0]],[[0,0],[0,0]],[[2839,374],[374,0]],[[0,0],[0,0]],[[51,408],[408,0]],[[0,0],[0,0]],[[-153,153],[153,0]],[[0],[0,0]],[[0],[0,17]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
