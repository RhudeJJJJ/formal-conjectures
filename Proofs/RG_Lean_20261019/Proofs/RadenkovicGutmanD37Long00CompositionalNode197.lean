/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode193
import Proofs.RadenkovicGutmanD37Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[215,0],[0,0]],[[0,0],[0,0]],[[2963,0],[0,0]],[[0,0],[0,0]],[[18028,0],[0,0]],[[0,0],[0,0]],[[60287,0],[0,0]],[[0,0],[0,0]],[[119172,2],[2,0]],[[0,0],[0,0]],[[141036,127],[127,0]],[[0,0],[0,0]],[[96608,858],[858,0]],[[0,0],[0,0]],[[34157,2046],[2046,0]],[[0,0],[0,0]],[[4089,1868],[1868,0]],[[0,0],[0,0]],[[-333,555],[555,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
