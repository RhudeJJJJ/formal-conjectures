/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode193
import Proofs.RadenkovicGutmanD33Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[195,0],[0,0]],[[0,0],[0,0]],[[2663,0],[0,0]],[[0,0],[0,0]],[[16148,0],[0,0]],[[0,0],[0,0]],[[53907,0],[0,0]],[[0,0],[0,0]],[[106452,2],[2,0]],[[0,0],[0,0]],[[125900,115],[115,0]],[[0,0],[0,0]],[[86200,770],[770,0]],[[0,0],[0,0]],[[30465,1830],[1830,0]],[[0,0],[0,0]],[[3645,1668],[1668,0]],[[0,0],[0,0]],[[-297,495],[495,2]],[[0],[0,0]],[[0],[0,33]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
