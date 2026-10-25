/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode160
import Proofs.RadenkovicGutmanD10Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-116,0],[0,0]],[[0,0],[0,0]],[[-696,0],[0,0]],[[0,0],[0,0]],[[-2228,0],[0,0]],[[0,0],[0,0]],[[-4088,0],[0,0]],[[0,0],[0,0]],[[-4272,-8],[-8,0]],[[0,0],[0,0]],[[-2280,-64],[-64,0]],[[0,0],[0,0]],[[-276,-176],[-176,0]],[[0,0],[0,0]],[[288,-192],[-192,0]],[[0,0],[0,0]],[[108,-72],[-72,0]],[[0],[0,0]],[[0],[0,-8]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
