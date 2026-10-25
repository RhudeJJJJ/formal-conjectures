/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode038
import Proofs.RadenkovicGutmanD8Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-6]],[[0,0],[0]],[[90,-54],[-54]],[[0,0],[0]],[[294,-144],[-144]],[[0,0],[0]],[[58,-132],[-132]],[[0,0],[0]],[[-1252,-48],[-48]],[[0,0],[0]],[[-2760,-6],[-6]],[[0]],[[-2816]],[[0]],[[-1590]],[[0]],[[-508]],[[0]],[[-86]],[[0]],[[-6]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
