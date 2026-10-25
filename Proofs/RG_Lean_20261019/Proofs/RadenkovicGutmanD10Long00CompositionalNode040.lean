/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode038
import Proofs.RadenkovicGutmanD10Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-8]],[[0,0],[0]],[[108,-72],[-72]],[[0,0],[0]],[[288,-192],[-192]],[[0,0],[0]],[[-276,-176],[-176]],[[0,0],[0]],[[-2280,-64],[-64]],[[0,0],[0]],[[-4272,-8],[-8]],[[0]],[[-4088]],[[0]],[[-2228]],[[0]],[[-696]],[[0]],[[-116]],[[0]],[[-8]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
