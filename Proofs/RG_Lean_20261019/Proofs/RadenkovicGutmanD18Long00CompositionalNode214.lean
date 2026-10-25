/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode030
import Proofs.RadenkovicGutmanD18Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[18],[0]],[[0,0],[0]],[[306,0],[0,0]],[[0,0],[0,0]],[[2196,0],[0,0]],[[0,0],[0,0]],[[8658,0],[0,0]],[[0,0],[0,0]],[[20448,0],[0,0]],[[0,0],[0,0]],[[29592,18],[18,0]],[[0,0],[0,0]],[[25740,144],[144,0]],[[0,0],[0,0]],[[12546,396],[396,0]],[[0,0],[0,0]],[[2862,432],[432,0]],[[0,0],[0,0]],[[162,162],[162,0]],[[0],[0,0]],[[0],[0,18]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
