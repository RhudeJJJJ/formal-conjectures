/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode203
import Proofs.RadenkovicGutmanD23Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[103,0],[0,0]],[[0,0],[0,0]],[[1371,0],[0,0]],[[0,0],[0,0]],[[8690,0],[0,0]],[[0,0],[0,0]],[[31183,0],[0,0]],[[0,0],[0,0]],[[67504,2],[2,0]],[[0,0],[0,0]],[[89248,85],[85,0]],[[0,0],[0,0]],[[70118,550],[550,0]],[[0,0],[0,0]],[[30149,1290],[1290,0]],[[0,0],[0,0]],[[5745,1168],[1168,0]],[[0,0],[0,0]],[[207,345],[345,2]],[[0],[0,0]],[[0],[0,23]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
