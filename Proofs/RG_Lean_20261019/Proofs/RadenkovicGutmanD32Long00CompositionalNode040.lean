/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode038
import Proofs.RadenkovicGutmanD32Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-30]],[[0,0],[0]],[[306,-270],[-270]],[[0,0],[0]],[[222,-720],[-720]],[[0,0],[0]],[[-3950,-660],[-660]],[[0,0],[0]],[[-13588,-240],[-240]],[[0,0],[0]],[[-20904,-30],[-30]],[[0]],[[-18080]],[[0]],[[-9246]],[[0]],[[-2764]],[[0]],[[-446]],[[0]],[[-30]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
