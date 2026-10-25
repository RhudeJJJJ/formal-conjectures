/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode203
import Proofs.RadenkovicGutmanD34Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[136,0],[0,0]],[[0,0],[0,0]],[[1910,0],[0,0]],[[0,0],[0,0]],[[12386,0],[0,0]],[[0,0],[0,0]],[[45010,0],[0,0]],[[0,0],[0,0]],[[98216,2],[2,0]],[[0,0],[0,0]],[[130564,118],[118,0]],[[0,0],[0,0]],[[102986,792],[792,0]],[[0,0],[0,0]],[[44416,1884],[1884,0]],[[0,0],[0,0]],[[8484,1718],[1718,0]],[[0,0],[0,0]],[[306,510],[510,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
