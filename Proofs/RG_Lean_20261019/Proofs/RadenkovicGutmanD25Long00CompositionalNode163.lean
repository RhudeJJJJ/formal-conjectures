/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode160
import Proofs.RadenkovicGutmanD25Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-23],[0]],[[0,0],[0]],[[-341,0],[0,0]],[[0,0],[0,0]],[[-2106,0],[0,0]],[[0,0],[0,0]],[[-7013,0],[0,0]],[[0,0],[0,0]],[[-13628,0],[0,0]],[[0,0],[0,0]],[[-15612,-23],[-23,0]],[[0,0],[0,0]],[[-9990,-184],[-184,0]],[[0,0],[0,0]],[[-2781,-506],[-506,0]],[[0,0],[0,0]],[[243,-552],[-552,0]],[[0,0],[0,0]],[[243,-207],[-207,0]],[[0],[0,0]],[[0],[0,-23]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
