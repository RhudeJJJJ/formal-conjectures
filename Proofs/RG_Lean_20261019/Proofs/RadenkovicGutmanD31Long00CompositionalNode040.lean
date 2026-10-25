/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode038
import Proofs.RadenkovicGutmanD31Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-29]],[[0,0],[0]],[[297,-261],[-261]],[[0,0],[0]],[[225,-696],[-696]],[[0,0],[0]],[[-3783,-638],[-638]],[[0,0],[0]],[[-13074,-232],[-232]],[[0,0],[0]],[[-20148,-29],[-29]],[[0]],[[-17444]],[[0]],[[-8927]],[[0]],[[-2670]],[[0]],[[-431]],[[0]],[[-29]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
