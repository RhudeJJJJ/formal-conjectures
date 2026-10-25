/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode193
import Proofs.RadenkovicGutmanD8Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[70,0],[0,0]],[[0,0],[0,0]],[[788,0],[0,0]],[[0,0],[0,0]],[[4398,0],[0,0]],[[0,0],[0,0]],[[14032,0],[0,0]],[[0,0],[0,0]],[[26952,2],[2,0]],[[0,0],[0,0]],[[31300,40],[40,0]],[[0,0],[0,0]],[[21150,220],[220,0]],[[0,0],[0,0]],[[7390,480],[480,0]],[[0,0],[0,0]],[[870,418],[418,0]],[[0,0],[0,0]],[[-72,120],[120,2]],[[0],[0,0]],[[0],[0,8]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
