/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode037
import Proofs.RadenkovicGutmanD15Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-13]],[[0,0],[0]],[[117,-117],[-117]],[[0,0],[0]],[[-39,-312],[-312]],[[0,0],[0]],[[-2171,-286],[-286]],[[0,0],[0]],[[-6682,-104],[-104]],[[0,0],[0]],[[-9828,-13],[-13]],[[0]],[[-8268]],[[0]],[[-4147]],[[0]],[[-1222]],[[0]],[[-195]],[[0]],[[-13]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
