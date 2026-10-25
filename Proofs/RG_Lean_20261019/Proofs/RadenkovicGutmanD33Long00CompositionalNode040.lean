/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode038
import Proofs.RadenkovicGutmanD33Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-31]],[[0,0],[0]],[[315,-279],[-279]],[[0,0],[0]],[[219,-744],[-744]],[[0,0],[0]],[[-4117,-682],[-682]],[[0,0],[0]],[[-14102,-248],[-248]],[[0,0],[0]],[[-21660,-31],[-31]],[[0]],[[-18716]],[[0]],[[-9565]],[[0]],[[-2858]],[[0]],[[-461]],[[0]],[[-31]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
