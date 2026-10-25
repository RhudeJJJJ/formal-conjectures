/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode038
import Proofs.RadenkovicGutmanD37Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-35]],[[0,0],[0]],[[351,-315],[-315]],[[0,0],[0]],[[207,-840],[-840]],[[0,0],[0]],[[-4785,-770],[-770]],[[0,0],[0]],[[-16158,-280],[-280]],[[0,0],[0]],[[-24684,-35],[-35]],[[0]],[[-21260]],[[0]],[[-10841]],[[0]],[[-3234]],[[0]],[[-521]],[[0]],[[-35]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
