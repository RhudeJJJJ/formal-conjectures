/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode202
import Proofs.RadenkovicGutmanD8Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[42,0],[0,0]],[[0,0],[0,0]],[[380,0],[0,0]],[[0,0],[0,0]],[[1938,0],[0,0]],[[0,0],[0,0]],[[6120,0],[0,0]],[[0,0],[0,0]],[[12376,2],[2,0]],[[0,0],[0,0]],[[16012,24],[24,0]],[[0,0],[0,0]],[[12834,108],[108,0]],[[0,0],[0,0]],[[5894,224],[224,0]],[[0,0],[0,0]],[[1290,210],[210,0]],[[0,0],[0,0]],[[72,72],[72,2]],[[0],[0,0]],[[0],[0,8]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
