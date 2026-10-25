/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode030
import Proofs.RadenkovicGutmanD11Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[11],[0]],[[0,0],[0]],[[187,0],[0,0]],[[0,0],[0,0]],[[1342,0],[0,0]],[[0,0],[0,0]],[[5291,0],[0,0]],[[0,0],[0,0]],[[12496,0],[0,0]],[[0,0],[0,0]],[[18084,11],[11,0]],[[0,0],[0,0]],[[15730,88],[88,0]],[[0,0],[0,0]],[[7667,242],[242,0]],[[0,0],[0,0]],[[1749,264],[264,0]],[[0,0],[0,0]],[[99,99],[99,0]],[[0],[0,0]],[[0],[0,11]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
