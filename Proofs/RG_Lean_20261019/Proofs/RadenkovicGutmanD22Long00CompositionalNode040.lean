/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode038
import Proofs.RadenkovicGutmanD22Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-20]],[[0,0],[0]],[[216,-180],[-180]],[[0,0],[0]],[[252,-480],[-480]],[[0,0],[0]],[[-2280,-440],[-440]],[[0,0],[0]],[[-8448,-160],[-160]],[[0,0],[0]],[[-13344,-20],[-20]],[[0]],[[-11720]],[[0]],[[-6056]],[[0]],[[-1824]],[[0]],[[-296]],[[0]],[[-20]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
