/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode030
import Proofs.RadenkovicGutmanD6Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[6],[0]],[[0,0],[0]],[[102,0],[0,0]],[[0,0],[0,0]],[[732,0],[0,0]],[[0,0],[0,0]],[[2886,0],[0,0]],[[0,0],[0,0]],[[6816,0],[0,0]],[[0,0],[0,0]],[[9864,6],[6,0]],[[0,0],[0,0]],[[8580,48],[48,0]],[[0,0],[0,0]],[[4182,132],[132,0]],[[0,0],[0,0]],[[954,144],[144,0]],[[0,0],[0,0]],[[54,54],[54,0]],[[0],[0,0]],[[0],[0,6]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
