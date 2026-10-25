/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode030
import Proofs.RadenkovicGutmanD9Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[9],[0]],[[0,0],[0]],[[153,0],[0,0]],[[0,0],[0,0]],[[1098,0],[0,0]],[[0,0],[0,0]],[[4329,0],[0,0]],[[0,0],[0,0]],[[10224,0],[0,0]],[[0,0],[0,0]],[[14796,9],[9,0]],[[0,0],[0,0]],[[12870,72],[72,0]],[[0,0],[0,0]],[[6273,198],[198,0]],[[0,0],[0,0]],[[1431,216],[216,0]],[[0,0],[0,0]],[[81,81],[81,0]],[[0],[0,0]],[[0],[0,9]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
