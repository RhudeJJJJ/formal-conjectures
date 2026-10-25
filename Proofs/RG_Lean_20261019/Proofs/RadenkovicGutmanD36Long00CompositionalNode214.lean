/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode030
import Proofs.RadenkovicGutmanD36Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[36],[0]],[[0,0],[0]],[[612,0],[0,0]],[[0,0],[0,0]],[[4392,0],[0,0]],[[0,0],[0,0]],[[17316,0],[0,0]],[[0,0],[0,0]],[[40896,0],[0,0]],[[0,0],[0,0]],[[59184,36],[36,0]],[[0,0],[0,0]],[[51480,288],[288,0]],[[0,0],[0,0]],[[25092,792],[792,0]],[[0,0],[0,0]],[[5724,864],[864,0]],[[0,0],[0,0]],[[324,324],[324,0]],[[0],[0,0]],[[0],[0,36]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
