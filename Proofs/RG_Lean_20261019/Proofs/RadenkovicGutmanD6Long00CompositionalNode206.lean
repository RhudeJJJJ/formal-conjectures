/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode203
import Proofs.RadenkovicGutmanD6Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[52,0],[0,0]],[[0,0],[0,0]],[[538,0],[0,0]],[[0,0],[0,0]],[[2978,0],[0,0]],[[0,0],[0,0]],[[9814,0],[0,0]],[[0,0],[0,0]],[[20040,2],[2,0]],[[0,0],[0,0]],[[25396,34],[34,0]],[[0,0],[0,0]],[[19322,176],[176,0]],[[0,0],[0,0]],[[8100,372],[372,0]],[[0,0],[0,0]],[[1512,318],[318,0]],[[0,0],[0,0]],[[54,90],[90,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
