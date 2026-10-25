/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode038
import Proofs.RadenkovicGutmanD38Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-36]],[[0,0],[0]],[[360,-324],[-324]],[[0,0],[0]],[[204,-864],[-864]],[[0,0],[0]],[[-4952,-792],[-792]],[[0,0],[0]],[[-16672,-288],[-288]],[[0,0],[0]],[[-25440,-36],[-36]],[[0]],[[-21896]],[[0]],[[-11160]],[[0]],[[-3328]],[[0]],[[-536]],[[0]],[[-36]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
