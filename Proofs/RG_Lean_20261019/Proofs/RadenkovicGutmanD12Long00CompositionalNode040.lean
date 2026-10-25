/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode038
import Proofs.RadenkovicGutmanD12Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-10]],[[0,0],[0]],[[126,-90],[-90]],[[0,0],[0]],[[282,-240],[-240]],[[0,0],[0]],[[-610,-220],[-220]],[[0,0],[0]],[[-3308,-80],[-80]],[[0,0],[0]],[[-5784,-10],[-10]],[[0]],[[-5360]],[[0]],[[-2866]],[[0]],[[-884]],[[0]],[[-146]],[[0]],[[-10]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
