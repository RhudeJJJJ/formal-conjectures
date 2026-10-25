/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode030
import Proofs.RadenkovicGutmanD38Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[38],[0]],[[0,0],[0]],[[646,0],[0,0]],[[0,0],[0,0]],[[4636,0],[0,0]],[[0,0],[0,0]],[[18278,0],[0,0]],[[0,0],[0,0]],[[43168,0],[0,0]],[[0,0],[0,0]],[[62472,38],[38,0]],[[0,0],[0,0]],[[54340,304],[304,0]],[[0,0],[0,0]],[[26486,836],[836,0]],[[0,0],[0,0]],[[6042,912],[912,0]],[[0,0],[0,0]],[[342,342],[342,0]],[[0],[0,0]],[[0],[0,38]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
