/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode030
import Proofs.RadenkovicGutmanD21Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[21],[0]],[[0,0],[0]],[[357,0],[0,0]],[[0,0],[0,0]],[[2562,0],[0,0]],[[0,0],[0,0]],[[10101,0],[0,0]],[[0,0],[0,0]],[[23856,0],[0,0]],[[0,0],[0,0]],[[34524,21],[21,0]],[[0,0],[0,0]],[[30030,168],[168,0]],[[0,0],[0,0]],[[14637,462],[462,0]],[[0,0],[0,0]],[[3339,504],[504,0]],[[0,0],[0,0]],[[189,189],[189,0]],[[0],[0,0]],[[0],[0,21]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
