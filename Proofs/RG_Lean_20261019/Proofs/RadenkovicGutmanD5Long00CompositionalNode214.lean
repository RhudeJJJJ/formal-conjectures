/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode030
import Proofs.RadenkovicGutmanD5Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[5],[0]],[[0,0],[0]],[[85,0],[0,0]],[[0,0],[0,0]],[[610,0],[0,0]],[[0,0],[0,0]],[[2405,0],[0,0]],[[0,0],[0,0]],[[5680,0],[0,0]],[[0,0],[0,0]],[[8220,5],[5,0]],[[0,0],[0,0]],[[7150,40],[40,0]],[[0,0],[0,0]],[[3485,110],[110,0]],[[0,0],[0,0]],[[795,120],[120,0]],[[0,0],[0,0]],[[45,45],[45,0]],[[0],[0,0]],[[0],[0,5]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
