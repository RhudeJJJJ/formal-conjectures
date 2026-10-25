/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode030
import Proofs.RadenkovicGutmanD19Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[19],[0]],[[0,0],[0]],[[323,0],[0,0]],[[0,0],[0,0]],[[2318,0],[0,0]],[[0,0],[0,0]],[[9139,0],[0,0]],[[0,0],[0,0]],[[21584,0],[0,0]],[[0,0],[0,0]],[[31236,19],[19,0]],[[0,0],[0,0]],[[27170,152],[152,0]],[[0,0],[0,0]],[[13243,418],[418,0]],[[0,0],[0,0]],[[3021,456],[456,0]],[[0,0],[0,0]],[[171,171],[171,0]],[[0],[0,0]],[[0],[0,19]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
