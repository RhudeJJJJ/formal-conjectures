/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode203
import Proofs.RadenkovicGutmanD16Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[82,0],[0,0]],[[0,0],[0,0]],[[1028,0],[0,0]],[[0,0],[0,0]],[[6338,0],[0,0]],[[0,0],[0,0]],[[22384,0],[0,0]],[[0,0],[0,0]],[[47960,2],[2,0]],[[0,0],[0,0]],[[62956,64],[64,0]],[[0,0],[0,0]],[[49202,396],[396,0]],[[0,0],[0,0]],[[21070,912],[912,0]],[[0,0],[0,0]],[[4002,818],[818,0]],[[0,0],[0,0]],[[144,240],[240,2]],[[0],[0,0]],[[0],[0,16]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
