/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode203
import Proofs.RadenkovicGutmanD24Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[106,0],[0,0]],[[0,0],[0,0]],[[1420,0],[0,0]],[[0,0],[0,0]],[[9026,0],[0,0]],[[0,0],[0,0]],[[32440,0],[0,0]],[[0,0],[0,0]],[[70296,2],[2,0]],[[0,0],[0,0]],[[93004,88],[88,0]],[[0,0],[0,0]],[[73106,572],[572,0]],[[0,0],[0,0]],[[31446,1344],[1344,0]],[[0,0],[0,0]],[[5994,1218],[1218,0]],[[0,0],[0,0]],[[216,360],[360,2]],[[0],[0,0]],[[0],[0,24]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
