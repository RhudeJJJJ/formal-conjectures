/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode038
import Proofs.RadenkovicGutmanD5Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-3]],[[0,0],[0]],[[63,-27],[-27]],[[0,0],[0]],[[303,-72],[-72]],[[0,0],[0]],[[559,-66],[-66]],[[0,0],[0]],[[290,-24],[-24]],[[0,0],[0]],[[-492,-3],[-3]],[[0]],[[-908]],[[0]],[[-633]],[[0]],[[-226]],[[0]],[[-41]],[[0]],[[-3]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
