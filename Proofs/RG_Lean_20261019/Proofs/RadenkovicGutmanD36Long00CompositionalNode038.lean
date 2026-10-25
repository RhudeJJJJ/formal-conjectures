/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode037
import Proofs.RadenkovicGutmanD36Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-34]],[[0,0],[0]],[[306,-306],[-306]],[[0,0],[0]],[[-102,-816],[-816]],[[0,0],[0]],[[-5678,-748],[-748]],[[0,0],[0]],[[-17476,-272],[-272]],[[0,0],[0]],[[-25704,-34],[-34]],[[0]],[[-21624]],[[0]],[[-10846]],[[0]],[[-3196]],[[0]],[[-510]],[[0]],[[-34]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
