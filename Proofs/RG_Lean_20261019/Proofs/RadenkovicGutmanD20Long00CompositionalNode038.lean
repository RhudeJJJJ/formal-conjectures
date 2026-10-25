/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode037
import Proofs.RadenkovicGutmanD20Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-18]],[[0,0],[0]],[[162,-162],[-162]],[[0,0],[0]],[[-54,-432],[-432]],[[0,0],[0]],[[-3006,-396],[-396]],[[0,0],[0]],[[-9252,-144],[-144]],[[0,0],[0]],[[-13608,-18],[-18]],[[0]],[[-11448]],[[0]],[[-5742]],[[0]],[[-1692]],[[0]],[[-270]],[[0]],[[-18]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
