/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode030
import Proofs.RadenkovicGutmanD33Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[33],[0]],[[0,0],[0]],[[561,0],[0,0]],[[0,0],[0,0]],[[4026,0],[0,0]],[[0,0],[0,0]],[[15873,0],[0,0]],[[0,0],[0,0]],[[37488,0],[0,0]],[[0,0],[0,0]],[[54252,33],[33,0]],[[0,0],[0,0]],[[47190,264],[264,0]],[[0,0],[0,0]],[[23001,726],[726,0]],[[0,0],[0,0]],[[5247,792],[792,0]],[[0,0],[0,0]],[[297,297],[297,0]],[[0],[0,0]],[[0],[0,33]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
