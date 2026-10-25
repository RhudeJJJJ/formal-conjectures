/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode038
import Proofs.RadenkovicGutmanD25Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-23]],[[0,0],[0]],[[243,-207],[-207]],[[0,0],[0]],[[243,-552],[-552]],[[0,0],[0]],[[-2781,-506],[-506]],[[0,0],[0]],[[-9990,-184],[-184]],[[0,0],[0]],[[-15612,-23],[-23]],[[0]],[[-13628]],[[0]],[[-7013]],[[0]],[[-2106]],[[0]],[[-341]],[[0]],[[-23]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
