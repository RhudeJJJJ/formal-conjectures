/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode037
import Proofs.RadenkovicGutmanD11Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-9]],[[0,0],[0]],[[81,-81],[-81]],[[0,0],[0]],[[-27,-216],[-216]],[[0,0],[0]],[[-1503,-198],[-198]],[[0,0],[0]],[[-4626,-72],[-72]],[[0,0],[0]],[[-6804,-9],[-9]],[[0]],[[-5724]],[[0]],[[-2871]],[[0]],[[-846]],[[0]],[[-135]],[[0]],[[-9]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
