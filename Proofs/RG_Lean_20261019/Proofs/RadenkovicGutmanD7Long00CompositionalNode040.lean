/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode038
import Proofs.RadenkovicGutmanD7Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-5]],[[0,0],[0]],[[81,-45],[-45]],[[0,0],[0]],[[297,-120],[-120]],[[0,0],[0]],[[225,-110],[-110]],[[0,0],[0]],[[-738,-40],[-40]],[[0,0],[0]],[[-2004,-5],[-5]],[[0]],[[-2180]],[[0]],[[-1271]],[[0]],[[-414]],[[0]],[[-71]],[[0]],[[-5]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
