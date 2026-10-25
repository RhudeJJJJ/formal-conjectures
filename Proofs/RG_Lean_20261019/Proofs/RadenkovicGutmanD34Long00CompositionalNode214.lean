/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode030
import Proofs.RadenkovicGutmanD34Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[34],[0]],[[0,0],[0]],[[578,0],[0,0]],[[0,0],[0,0]],[[4148,0],[0,0]],[[0,0],[0,0]],[[16354,0],[0,0]],[[0,0],[0,0]],[[38624,0],[0,0]],[[0,0],[0,0]],[[55896,34],[34,0]],[[0,0],[0,0]],[[48620,272],[272,0]],[[0,0],[0,0]],[[23698,748],[748,0]],[[0,0],[0,0]],[[5406,816],[816,0]],[[0,0],[0,0]],[[306,306],[306,0]],[[0],[0,0]],[[0],[0,34]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
