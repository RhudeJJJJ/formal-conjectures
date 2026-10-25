/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode030
import Proofs.RadenkovicGutmanD37Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[37],[0]],[[0,0],[0]],[[629,0],[0,0]],[[0,0],[0,0]],[[4514,0],[0,0]],[[0,0],[0,0]],[[17797,0],[0,0]],[[0,0],[0,0]],[[42032,0],[0,0]],[[0,0],[0,0]],[[60828,37],[37,0]],[[0,0],[0,0]],[[52910,296],[296,0]],[[0,0],[0,0]],[[25789,814],[814,0]],[[0,0],[0,0]],[[5883,888],[888,0]],[[0,0],[0,0]],[[333,333],[333,0]],[[0],[0,0]],[[0],[0,37]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
