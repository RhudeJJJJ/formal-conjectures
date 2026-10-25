/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode030
import Proofs.RadenkovicGutmanD43Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[43],[0]],[[0,0],[0]],[[731,0],[0,0]],[[0,0],[0,0]],[[5246,0],[0,0]],[[0,0],[0,0]],[[20683,0],[0,0]],[[0,0],[0,0]],[[48848,0],[0,0]],[[0,0],[0,0]],[[70692,43],[43,0]],[[0,0],[0,0]],[[61490,344],[344,0]],[[0,0],[0,0]],[[29971,946],[946,0]],[[0,0],[0,0]],[[6837,1032],[1032,0]],[[0,0],[0,0]],[[387,387],[387,0]],[[0],[0,0]],[[0],[0,43]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
