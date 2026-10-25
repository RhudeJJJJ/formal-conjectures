/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode203
import Proofs.RadenkovicGutmanD7Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[55,0],[0,0]],[[0,0],[0,0]],[[587,0],[0,0]],[[0,0],[0,0]],[[3314,0],[0,0]],[[0,0],[0,0]],[[11071,0],[0,0]],[[0,0],[0,0]],[[22832,2],[2,0]],[[0,0],[0,0]],[[29152,37],[37,0]],[[0,0],[0,0]],[[22310,198],[198,0]],[[0,0],[0,0]],[[9397,426],[426,0]],[[0,0],[0,0]],[[1761,368],[368,0]],[[0,0],[0,0]],[[63,105],[105,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
