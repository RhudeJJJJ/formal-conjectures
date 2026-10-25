/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode030
import Proofs.RadenkovicGutmanD30Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[30],[0]],[[0,0],[0]],[[510,0],[0,0]],[[0,0],[0,0]],[[3660,0],[0,0]],[[0,0],[0,0]],[[14430,0],[0,0]],[[0,0],[0,0]],[[34080,0],[0,0]],[[0,0],[0,0]],[[49320,30],[30,0]],[[0,0],[0,0]],[[42900,240],[240,0]],[[0,0],[0,0]],[[20910,660],[660,0]],[[0,0],[0,0]],[[4770,720],[720,0]],[[0,0],[0,0]],[[270,270],[270,0]],[[0],[0,0]],[[0],[0,30]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
