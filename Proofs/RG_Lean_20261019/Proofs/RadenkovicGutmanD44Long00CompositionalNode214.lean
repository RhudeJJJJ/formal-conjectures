/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode030
import Proofs.RadenkovicGutmanD44Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[44],[0]],[[0,0],[0]],[[748,0],[0,0]],[[0,0],[0,0]],[[5368,0],[0,0]],[[0,0],[0,0]],[[21164,0],[0,0]],[[0,0],[0,0]],[[49984,0],[0,0]],[[0,0],[0,0]],[[72336,44],[44,0]],[[0,0],[0,0]],[[62920,352],[352,0]],[[0,0],[0,0]],[[30668,968],[968,0]],[[0,0],[0,0]],[[6996,1056],[1056,0]],[[0,0],[0,0]],[[396,396],[396,0]],[[0],[0,0]],[[0],[0,44]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
