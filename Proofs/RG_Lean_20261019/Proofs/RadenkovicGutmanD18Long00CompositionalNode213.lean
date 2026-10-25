/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode030
import Proofs.RadenkovicGutmanD18Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[18],[0]],[[0,0],[0]],[[270,0],[0,0]],[[0,0],[0,0]],[[1692,0],[0,0]],[[0,0],[0,0]],[[5742,0],[0,0]],[[0,0],[0,0]],[[11448,0],[0,0]],[[0,0],[0,0]],[[13608,18],[18,0]],[[0,0],[0,0]],[[9252,144],[144,0]],[[0,0],[0,0]],[[3006,396],[396,0]],[[0,0],[0,0]],[[54,432],[432,0]],[[0,0],[0,0]],[[-162,162],[162,0]],[[0],[0,0]],[[0],[0,18]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
