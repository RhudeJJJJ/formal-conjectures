/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode038
import Proofs.RadenkovicGutmanD34Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-32]],[[0,0],[0]],[[324,-288],[-288]],[[0,0],[0]],[[216,-768],[-768]],[[0,0],[0]],[[-4284,-704],[-704]],[[0,0],[0]],[[-14616,-256],[-256]],[[0,0],[0]],[[-22416,-32],[-32]],[[0]],[[-19352]],[[0]],[[-9884]],[[0]],[[-2952]],[[0]],[[-476]],[[0]],[[-32]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
