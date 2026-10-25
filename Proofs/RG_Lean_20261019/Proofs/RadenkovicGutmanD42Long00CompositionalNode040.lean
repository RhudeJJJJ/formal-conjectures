/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode038
import Proofs.RadenkovicGutmanD42Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-40]],[[0,0],[0]],[[396,-360],[-360]],[[0,0],[0]],[[192,-960],[-960]],[[0,0],[0]],[[-5620,-880],[-880]],[[0,0],[0]],[[-18728,-320],[-320]],[[0,0],[0]],[[-28464,-40],[-40]],[[0]],[[-24440]],[[0]],[[-12436]],[[0]],[[-3704]],[[0]],[[-596]],[[0]],[[-40]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
