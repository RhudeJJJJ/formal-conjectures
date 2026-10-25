/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode038
import Proofs.RadenkovicGutmanD18Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-16]],[[0,0],[0]],[[180,-144],[-144]],[[0,0],[0]],[[264,-384],[-384]],[[0,0],[0]],[[-1612,-352],[-352]],[[0,0],[0]],[[-6392,-128],[-128]],[[0,0],[0]],[[-10320,-16],[-16]],[[0]],[[-9176]],[[0]],[[-4780]],[[0]],[[-1448]],[[0]],[[-236]],[[0]],[[-16]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
