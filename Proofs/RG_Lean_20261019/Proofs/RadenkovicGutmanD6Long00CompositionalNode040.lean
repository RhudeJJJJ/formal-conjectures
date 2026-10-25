/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode038
import Proofs.RadenkovicGutmanD6Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-4]],[[0,0],[0]],[[72,-36],[-36]],[[0,0],[0]],[[300,-96],[-96]],[[0,0],[0]],[[392,-88],[-88]],[[0,0],[0]],[[-224,-32],[-32]],[[0,0],[0]],[[-1248,-4],[-4]],[[0]],[[-1544]],[[0]],[[-952]],[[0]],[[-320]],[[0]],[[-56]],[[0]],[[-4]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
