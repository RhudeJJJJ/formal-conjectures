/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode038
import Proofs.RadenkovicGutmanD41Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-39]],[[0,0],[0]],[[387,-351],[-351]],[[0,0],[0]],[[195,-936],[-936]],[[0,0],[0]],[[-5453,-858],[-858]],[[0,0],[0]],[[-18214,-312],[-312]],[[0,0],[0]],[[-27708,-39],[-39]],[[0]],[[-23804]],[[0]],[[-12117]],[[0]],[[-3610]],[[0]],[[-581]],[[0]],[[-39]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
