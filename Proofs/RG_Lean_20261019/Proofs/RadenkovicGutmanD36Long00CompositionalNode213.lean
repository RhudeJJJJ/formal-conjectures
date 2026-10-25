/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode030
import Proofs.RadenkovicGutmanD36Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[36],[0]],[[0,0],[0]],[[540,0],[0,0]],[[0,0],[0,0]],[[3384,0],[0,0]],[[0,0],[0,0]],[[11484,0],[0,0]],[[0,0],[0,0]],[[22896,0],[0,0]],[[0,0],[0,0]],[[27216,36],[36,0]],[[0,0],[0,0]],[[18504,288],[288,0]],[[0,0],[0,0]],[[6012,792],[792,0]],[[0,0],[0,0]],[[108,864],[864,0]],[[0,0],[0,0]],[[-324,324],[324,0]],[[0],[0,0]],[[0],[0,36]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
