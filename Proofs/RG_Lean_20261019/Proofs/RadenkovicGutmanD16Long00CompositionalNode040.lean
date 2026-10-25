/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode038
import Proofs.RadenkovicGutmanD16Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-14]],[[0,0],[0]],[[162,-126],[-126]],[[0,0],[0]],[[270,-336],[-336]],[[0,0],[0]],[[-1278,-308],[-308]],[[0,0],[0]],[[-5364,-112],[-112]],[[0,0],[0]],[[-8808,-14],[-14]],[[0]],[[-7904]],[[0]],[[-4142]],[[0]],[[-1260]],[[0]],[[-206]],[[0]],[[-14]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
