/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode030
import Proofs.RadenkovicGutmanD7Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[7],[0]],[[0,0],[0]],[[119,0],[0,0]],[[0,0],[0,0]],[[854,0],[0,0]],[[0,0],[0,0]],[[3367,0],[0,0]],[[0,0],[0,0]],[[7952,0],[0,0]],[[0,0],[0,0]],[[11508,7],[7,0]],[[0,0],[0,0]],[[10010,56],[56,0]],[[0,0],[0,0]],[[4879,154],[154,0]],[[0,0],[0,0]],[[1113,168],[168,0]],[[0,0],[0,0]],[[63,63],[63,0]],[[0],[0,0]],[[0],[0,7]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
