/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode193
import Proofs.RadenkovicGutmanD15Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[105,0],[0,0]],[[0,0],[0,0]],[[1313,0],[0,0]],[[0,0],[0,0]],[[7688,0],[0,0]],[[0,0],[0,0]],[[25197,0],[0,0]],[[0,0],[0,0]],[[49212,2],[2,0]],[[0,0],[0,0]],[[57788,61],[61,0]],[[0,0],[0,0]],[[39364,374],[374,0]],[[0,0],[0,0]],[[13851,858],[858,0]],[[0,0],[0,0]],[[1647,768],[768,0]],[[0,0],[0,0]],[[-135,225],[225,2]],[[0],[0,0]],[[0],[0,15]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
