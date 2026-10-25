/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode193
import Proofs.RadenkovicGutmanD16Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[110,0],[0,0]],[[0,0],[0,0]],[[1388,0],[0,0]],[[0,0],[0,0]],[[8158,0],[0,0]],[[0,0],[0,0]],[[26792,0],[0,0]],[[0,0],[0,0]],[[52392,2],[2,0]],[[0,0],[0,0]],[[61572,64],[64,0]],[[0,0],[0,0]],[[41966,396],[396,0]],[[0,0],[0,0]],[[14774,912],[912,0]],[[0,0],[0,0]],[[1758,818],[818,0]],[[0,0],[0,0]],[[-144,240],[240,2]],[[0],[0,0]],[[0],[0,16]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
