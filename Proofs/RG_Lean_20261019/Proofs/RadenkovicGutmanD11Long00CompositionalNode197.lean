/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode193
import Proofs.RadenkovicGutmanD11Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[85,0],[0,0]],[[0,0],[0,0]],[[1013,0],[0,0]],[[0,0],[0,0]],[[5808,0],[0,0]],[[0,0],[0,0]],[[18817,0],[0,0]],[[0,0],[0,0]],[[36492,2],[2,0]],[[0,0],[0,0]],[[42652,49],[49,0]],[[0,0],[0,0]],[[28956,286],[286,0]],[[0,0],[0,0]],[[10159,642],[642,0]],[[0,0],[0,0]],[[1203,568],[568,0]],[[0,0],[0,0]],[[-99,165],[165,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
