/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode030
import Proofs.RadenkovicGutmanD33Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[33],[0]],[[0,0],[0]],[[495,0],[0,0]],[[0,0],[0,0]],[[3102,0],[0,0]],[[0,0],[0,0]],[[10527,0],[0,0]],[[0,0],[0,0]],[[20988,0],[0,0]],[[0,0],[0,0]],[[24948,33],[33,0]],[[0,0],[0,0]],[[16962,264],[264,0]],[[0,0],[0,0]],[[5511,726],[726,0]],[[0,0],[0,0]],[[99,792],[792,0]],[[0,0],[0,0]],[[-297,297],[297,0]],[[0],[0,0]],[[0],[0,33]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
