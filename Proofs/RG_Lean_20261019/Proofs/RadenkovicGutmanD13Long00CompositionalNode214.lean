/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode030
import Proofs.RadenkovicGutmanD13Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[13],[0]],[[0,0],[0]],[[221,0],[0,0]],[[0,0],[0,0]],[[1586,0],[0,0]],[[0,0],[0,0]],[[6253,0],[0,0]],[[0,0],[0,0]],[[14768,0],[0,0]],[[0,0],[0,0]],[[21372,13],[13,0]],[[0,0],[0,0]],[[18590,104],[104,0]],[[0,0],[0,0]],[[9061,286],[286,0]],[[0,0],[0,0]],[[2067,312],[312,0]],[[0,0],[0,0]],[[117,117],[117,0]],[[0],[0,0]],[[0],[0,13]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
