/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode193
import Proofs.RadenkovicGutmanD35Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[205,0],[0,0]],[[0,0],[0,0]],[[2813,0],[0,0]],[[0,0],[0,0]],[[17088,0],[0,0]],[[0,0],[0,0]],[[57097,0],[0,0]],[[0,0],[0,0]],[[112812,2],[2,0]],[[0,0],[0,0]],[[133468,121],[121,0]],[[0,0],[0,0]],[[91404,814],[814,0]],[[0,0],[0,0]],[[32311,1938],[1938,0]],[[0,0],[0,0]],[[3867,1768],[1768,0]],[[0,0],[0,0]],[[-315,525],[525,2]],[[0],[0,0]],[[0],[0,35]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
