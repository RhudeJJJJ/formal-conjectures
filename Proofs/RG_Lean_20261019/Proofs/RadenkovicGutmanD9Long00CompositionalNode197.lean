/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode193
import Proofs.RadenkovicGutmanD9Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[75,0],[0,0]],[[0,0],[0,0]],[[863,0],[0,0]],[[0,0],[0,0]],[[4868,0],[0,0]],[[0,0],[0,0]],[[15627,0],[0,0]],[[0,0],[0,0]],[[30132,2],[2,0]],[[0,0],[0,0]],[[35084,43],[43,0]],[[0,0],[0,0]],[[23752,242],[242,0]],[[0,0],[0,0]],[[8313,534],[534,0]],[[0,0],[0,0]],[[981,468],[468,0]],[[0,0],[0,0]],[[-81,135],[135,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
