/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode203
import Proofs.RadenkovicGutmanD5Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[49,0],[0,0]],[[0,0],[0,0]],[[489,0],[0,0]],[[0,0],[0,0]],[[2642,0],[0,0]],[[0,0],[0,0]],[[8557,0],[0,0]],[[0,0],[0,0]],[[17248,2],[2,0]],[[0,0],[0,0]],[[21640,31],[31,0]],[[0,0],[0,0]],[[16334,154],[154,0]],[[0,0],[0,0]],[[6803,318],[318,0]],[[0,0],[0,0]],[[1263,268],[268,0]],[[0,0],[0,0]],[[45,75],[75,2]],[[0],[0,0]],[[0],[0,5]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
