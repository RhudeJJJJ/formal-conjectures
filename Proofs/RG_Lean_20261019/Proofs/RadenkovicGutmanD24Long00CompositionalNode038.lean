/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode037
import Proofs.RadenkovicGutmanD24Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-22]],[[0,0],[0]],[[198,-198],[-198]],[[0,0],[0]],[[-66,-528],[-528]],[[0,0],[0]],[[-3674,-484],[-484]],[[0,0],[0]],[[-11308,-176],[-176]],[[0,0],[0]],[[-16632,-22],[-22]],[[0]],[[-13992]],[[0]],[[-7018]],[[0]],[[-2068]],[[0]],[[-330]],[[0]],[[-22]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
