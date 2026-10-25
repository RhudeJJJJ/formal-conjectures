/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode038
import Proofs.RadenkovicGutmanD9Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-7]],[[0,0],[0]],[[99,-63],[-63]],[[0,0],[0]],[[291,-168],[-168]],[[0,0],[0]],[[-109,-154],[-154]],[[0,0],[0]],[[-1766,-56],[-56]],[[0,0],[0]],[[-3516,-7],[-7]],[[0]],[[-3452]],[[0]],[[-1909]],[[0]],[[-602]],[[0]],[[-101]],[[0]],[[-7]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
