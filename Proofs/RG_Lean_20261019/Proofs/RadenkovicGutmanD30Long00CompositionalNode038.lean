/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode037
import Proofs.RadenkovicGutmanD30Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-28]],[[0,0],[0]],[[252,-252],[-252]],[[0,0],[0]],[[-84,-672],[-672]],[[0,0],[0]],[[-4676,-616],[-616]],[[0,0],[0]],[[-14392,-224],[-224]],[[0,0],[0]],[[-21168,-28],[-28]],[[0]],[[-17808]],[[0]],[[-8932]],[[0]],[[-2632]],[[0]],[[-420]],[[0]],[[-28]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
