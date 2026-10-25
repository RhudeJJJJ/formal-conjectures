/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode193
import Proofs.RadenkovicGutmanD32Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[190,0],[0,0]],[[0,0],[0,0]],[[2588,0],[0,0]],[[0,0],[0,0]],[[15678,0],[0,0]],[[0,0],[0,0]],[[52312,0],[0,0]],[[0,0],[0,0]],[[103272,2],[2,0]],[[0,0],[0,0]],[[122116,112],[112,0]],[[0,0],[0,0]],[[83598,748],[748,0]],[[0,0],[0,0]],[[29542,1776],[1776,0]],[[0,0],[0,0]],[[3534,1618],[1618,0]],[[0,0],[0,0]],[[-288,480],[480,2]],[[0],[0,0]],[[0],[0,32]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
