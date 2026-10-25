/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode030
import Proofs.RadenkovicGutmanD35Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[35],[0]],[[0,0],[0]],[[595,0],[0,0]],[[0,0],[0,0]],[[4270,0],[0,0]],[[0,0],[0,0]],[[16835,0],[0,0]],[[0,0],[0,0]],[[39760,0],[0,0]],[[0,0],[0,0]],[[57540,35],[35,0]],[[0,0],[0,0]],[[50050,280],[280,0]],[[0,0],[0,0]],[[24395,770],[770,0]],[[0,0],[0,0]],[[5565,840],[840,0]],[[0,0],[0,0]],[[315,315],[315,0]],[[0],[0,0]],[[0],[0,35]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
