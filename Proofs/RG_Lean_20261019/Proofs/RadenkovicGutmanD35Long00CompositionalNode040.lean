/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode038
import Proofs.RadenkovicGutmanD35Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-33]],[[0,0],[0]],[[333,-297],[-297]],[[0,0],[0]],[[213,-792],[-792]],[[0,0],[0]],[[-4451,-726],[-726]],[[0,0],[0]],[[-15130,-264],[-264]],[[0,0],[0]],[[-23172,-33],[-33]],[[0]],[[-19988]],[[0]],[[-10203]],[[0]],[[-3046]],[[0]],[[-491]],[[0]],[[-33]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
