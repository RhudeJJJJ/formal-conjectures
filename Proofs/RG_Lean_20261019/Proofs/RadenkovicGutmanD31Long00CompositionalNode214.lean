/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode030
import Proofs.RadenkovicGutmanD31Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[31],[0]],[[0,0],[0]],[[527,0],[0,0]],[[0,0],[0,0]],[[3782,0],[0,0]],[[0,0],[0,0]],[[14911,0],[0,0]],[[0,0],[0,0]],[[35216,0],[0,0]],[[0,0],[0,0]],[[50964,31],[31,0]],[[0,0],[0,0]],[[44330,248],[248,0]],[[0,0],[0,0]],[[21607,682],[682,0]],[[0,0],[0,0]],[[4929,744],[744,0]],[[0,0],[0,0]],[[279,279],[279,0]],[[0],[0,0]],[[0],[0,31]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
