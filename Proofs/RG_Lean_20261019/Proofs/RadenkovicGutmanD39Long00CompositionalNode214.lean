/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode030
import Proofs.RadenkovicGutmanD39Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[39],[0]],[[0,0],[0]],[[663,0],[0,0]],[[0,0],[0,0]],[[4758,0],[0,0]],[[0,0],[0,0]],[[18759,0],[0,0]],[[0,0],[0,0]],[[44304,0],[0,0]],[[0,0],[0,0]],[[64116,39],[39,0]],[[0,0],[0,0]],[[55770,312],[312,0]],[[0,0],[0,0]],[[27183,858],[858,0]],[[0,0],[0,0]],[[6201,936],[936,0]],[[0,0],[0,0]],[[351,351],[351,0]],[[0],[0,0]],[[0],[0,39]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
