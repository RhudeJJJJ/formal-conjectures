/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode030
import Proofs.RadenkovicGutmanD17Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,17]],[[0,0],[0]],[[-153,153],[153]],[[0,0],[0]],[[51,408],[408]],[[0,0],[0]],[[2839,374],[374]],[[0,0],[0]],[[8738,136],[136]],[[0,0],[0]],[[12852,17],[17]],[[0]],[[10812]],[[0]],[[5423]],[[0]],[[1598]],[[0]],[[255]],[[0]],[[17]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
