/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode193
import Proofs.RadenkovicGutmanD10Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[80,0],[0,0]],[[0,0],[0,0]],[[938,0],[0,0]],[[0,0],[0,0]],[[5338,0],[0,0]],[[0,0],[0,0]],[[17222,0],[0,0]],[[0,0],[0,0]],[[33312,2],[2,0]],[[0,0],[0,0]],[[38868,46],[46,0]],[[0,0],[0,0]],[[26354,264],[264,0]],[[0,0],[0,0]],[[9236,588],[588,0]],[[0,0],[0,0]],[[1092,518],[518,0]],[[0,0],[0,0]],[[-90,150],[150,2]],[[0],[0,0]],[[0],[0,10]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
