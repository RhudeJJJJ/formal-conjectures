/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode038
import Proofs.RadenkovicGutmanD23Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-21]],[[0,0],[0]],[[225,-189],[-189]],[[0,0],[0]],[[249,-504],[-504]],[[0,0],[0]],[[-2447,-462],[-462]],[[0,0],[0]],[[-8962,-168],[-168]],[[0,0],[0]],[[-14100,-21],[-21]],[[0]],[[-12356]],[[0]],[[-6375]],[[0]],[[-1918]],[[0]],[[-311]],[[0]],[[-21]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
