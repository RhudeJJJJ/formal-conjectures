/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode045
import Proofs.RadenkovicGutmanD11Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,11]],[[0,0],[0,0]],[[-99,165],[165,2]],[[0,0],[0]],[[1203,568],[568]],[[0,0],[0]],[[10159,642],[642]],[[0,0],[0]],[[28956,286],[286]],[[0,0],[0]],[[42652,49],[49]],[[0,0],[0]],[[36492,2],[2]],[[0]],[[18817]],[[0]],[[5808]],[[0]],[[1013]],[[0]],[[85]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
