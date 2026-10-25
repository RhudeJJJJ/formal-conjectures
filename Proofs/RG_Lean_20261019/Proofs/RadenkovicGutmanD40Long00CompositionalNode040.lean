/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode038
import Proofs.RadenkovicGutmanD40Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-38]],[[0,0],[0]],[[378,-342],[-342]],[[0,0],[0]],[[198,-912],[-912]],[[0,0],[0]],[[-5286,-836],[-836]],[[0,0],[0]],[[-17700,-304],[-304]],[[0,0],[0]],[[-26952,-38],[-38]],[[0]],[[-23168]],[[0]],[[-11798]],[[0]],[[-3516]],[[0]],[[-566]],[[0]],[[-38]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
