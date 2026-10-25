/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode193
import Proofs.RadenkovicGutmanD24Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[150,0],[0,0]],[[0,0],[0,0]],[[1988,0],[0,0]],[[0,0],[0,0]],[[11918,0],[0,0]],[[0,0],[0,0]],[[39552,0],[0,0]],[[0,0],[0,0]],[[77832,2],[2,0]],[[0,0],[0,0]],[[91844,88],[88,0]],[[0,0],[0,0]],[[62782,572],[572,0]],[[0,0],[0,0]],[[22158,1344],[1344,0]],[[0,0],[0,0]],[[2646,1218],[1218,0]],[[0,0],[0,0]],[[-216,360],[360,2]],[[0],[0,0]],[[0],[0,24]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
