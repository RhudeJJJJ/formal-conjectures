/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode038
import Proofs.RadenkovicGutmanD36Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-34]],[[0,0],[0]],[[342,-306],[-306]],[[0,0],[0]],[[210,-816],[-816]],[[0,0],[0]],[[-4618,-748],[-748]],[[0,0],[0]],[[-15644,-272],[-272]],[[0,0],[0]],[[-23928,-34],[-34]],[[0]],[[-20624]],[[0]],[[-10522]],[[0]],[[-3140]],[[0]],[[-506]],[[0]],[[-34]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
