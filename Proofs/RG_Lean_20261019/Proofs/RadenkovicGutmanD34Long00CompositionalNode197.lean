/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode193
import Proofs.RadenkovicGutmanD34Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[200,0],[0,0]],[[0,0],[0,0]],[[2738,0],[0,0]],[[0,0],[0,0]],[[16618,0],[0,0]],[[0,0],[0,0]],[[55502,0],[0,0]],[[0,0],[0,0]],[[109632,2],[2,0]],[[0,0],[0,0]],[[129684,118],[118,0]],[[0,0],[0,0]],[[88802,792],[792,0]],[[0,0],[0,0]],[[31388,1884],[1884,0]],[[0,0],[0,0]],[[3756,1718],[1718,0]],[[0,0],[0,0]],[[-306,510],[510,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
