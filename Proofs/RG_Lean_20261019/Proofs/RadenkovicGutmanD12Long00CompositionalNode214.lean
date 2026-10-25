/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode030
import Proofs.RadenkovicGutmanD12Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[12],[0]],[[0,0],[0]],[[204,0],[0,0]],[[0,0],[0,0]],[[1464,0],[0,0]],[[0,0],[0,0]],[[5772,0],[0,0]],[[0,0],[0,0]],[[13632,0],[0,0]],[[0,0],[0,0]],[[19728,12],[12,0]],[[0,0],[0,0]],[[17160,96],[96,0]],[[0,0],[0,0]],[[8364,264],[264,0]],[[0,0],[0,0]],[[1908,288],[288,0]],[[0,0],[0,0]],[[108,108],[108,0]],[[0],[0,0]],[[0],[0,12]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
