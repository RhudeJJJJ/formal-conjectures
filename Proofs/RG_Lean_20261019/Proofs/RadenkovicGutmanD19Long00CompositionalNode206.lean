/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode203
import Proofs.RadenkovicGutmanD19Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[91,0],[0,0]],[[0,0],[0,0]],[[1175,0],[0,0]],[[0,0],[0,0]],[[7346,0],[0,0]],[[0,0],[0,0]],[[26155,0],[0,0]],[[0,0],[0,0]],[[56336,2],[2,0]],[[0,0],[0,0]],[[74224,73],[73,0]],[[0,0],[0,0]],[[58166,462],[462,0]],[[0,0],[0,0]],[[24961,1074],[1074,0]],[[0,0],[0,0]],[[4749,968],[968,0]],[[0,0],[0,0]],[[171,285],[285,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
