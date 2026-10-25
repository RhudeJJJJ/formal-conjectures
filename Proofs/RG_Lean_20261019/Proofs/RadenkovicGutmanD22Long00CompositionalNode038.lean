/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode037
import Proofs.RadenkovicGutmanD22Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-20]],[[0,0],[0]],[[180,-180],[-180]],[[0,0],[0]],[[-60,-480],[-480]],[[0,0],[0]],[[-3340,-440],[-440]],[[0,0],[0]],[[-10280,-160],[-160]],[[0,0],[0]],[[-15120,-20],[-20]],[[0]],[[-12720]],[[0]],[[-6380]],[[0]],[[-1880]],[[0]],[[-300]],[[0]],[[-20]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
