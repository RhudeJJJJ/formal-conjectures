/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode038
import Proofs.RadenkovicGutmanD20Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-18]],[[0,0],[0]],[[198,-162],[-162]],[[0,0],[0]],[[258,-432],[-432]],[[0,0],[0]],[[-1946,-396],[-396]],[[0,0],[0]],[[-7420,-144],[-144]],[[0,0],[0]],[[-11832,-18],[-18]],[[0]],[[-10448]],[[0]],[[-5418]],[[0]],[[-1636]],[[0]],[[-266]],[[0]],[[-18]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
