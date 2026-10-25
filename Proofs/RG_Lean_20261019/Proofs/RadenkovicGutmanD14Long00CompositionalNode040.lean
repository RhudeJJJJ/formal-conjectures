/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode038
import Proofs.RadenkovicGutmanD14Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-12]],[[0,0],[0]],[[144,-108],[-108]],[[0,0],[0]],[[276,-288],[-288]],[[0,0],[0]],[[-944,-264],[-264]],[[0,0],[0]],[[-4336,-96],[-96]],[[0,0],[0]],[[-7296,-12],[-12]],[[0]],[[-6632]],[[0]],[[-3504]],[[0]],[[-1072]],[[0]],[[-176]],[[0]],[[-12]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
