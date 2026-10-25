/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode037
import Proofs.RadenkovicGutmanD42Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-40]],[[0,0],[0]],[[360,-360],[-360]],[[0,0],[0]],[[-120,-960],[-960]],[[0,0],[0]],[[-6680,-880],[-880]],[[0,0],[0]],[[-20560,-320],[-320]],[[0,0],[0]],[[-30240,-40],[-40]],[[0]],[[-25440]],[[0]],[[-12760]],[[0]],[[-3760]],[[0]],[[-600]],[[0]],[[-40]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
