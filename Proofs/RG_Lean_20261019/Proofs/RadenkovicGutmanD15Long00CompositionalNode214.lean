/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode030
import Proofs.RadenkovicGutmanD15Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[15],[0]],[[0,0],[0]],[[255,0],[0,0]],[[0,0],[0,0]],[[1830,0],[0,0]],[[0,0],[0,0]],[[7215,0],[0,0]],[[0,0],[0,0]],[[17040,0],[0,0]],[[0,0],[0,0]],[[24660,15],[15,0]],[[0,0],[0,0]],[[21450,120],[120,0]],[[0,0],[0,0]],[[10455,330],[330,0]],[[0,0],[0,0]],[[2385,360],[360,0]],[[0,0],[0,0]],[[135,135],[135,0]],[[0],[0,0]],[[0],[0,15]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
