/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode191
import Proofs.RadenkovicGutmanD8Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[42,0],[0,0]],[[0,0],[0,0]],[[380,0],[0,0]],[[0,0],[0,0]],[[1938,0],[0,0]],[[0,0],[0,0]],[[6120,0],[0,0]],[[0,0],[0,0]],[[12376,2],[2,0]],[[0,0],[0,0]],[[16012,24],[24,0]],[[0,0],[0,0]],[[12834,108],[108,0]],[[0,0],[0,0]],[[5894,224],[224,0]],[[0,0],[0,0]],[[1290,210],[210,0]],[[0,0],[0,0]],[[72,72],[72,2]],[[0],[0,0]],[[0],[0,8]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
