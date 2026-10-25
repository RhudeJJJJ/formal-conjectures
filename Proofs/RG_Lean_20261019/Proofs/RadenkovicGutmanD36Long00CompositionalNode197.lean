/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode193
import Proofs.RadenkovicGutmanD36Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[210,0],[0,0]],[[0,0],[0,0]],[[2888,0],[0,0]],[[0,0],[0,0]],[[17558,0],[0,0]],[[0,0],[0,0]],[[58692,0],[0,0]],[[0,0],[0,0]],[[115992,2],[2,0]],[[0,0],[0,0]],[[137252,124],[124,0]],[[0,0],[0,0]],[[94006,836],[836,0]],[[0,0],[0,0]],[[33234,1992],[1992,0]],[[0,0],[0,0]],[[3978,1818],[1818,0]],[[0,0],[0,0]],[[-324,540],[540,2]],[[0],[0,0]],[[0],[0,36]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
