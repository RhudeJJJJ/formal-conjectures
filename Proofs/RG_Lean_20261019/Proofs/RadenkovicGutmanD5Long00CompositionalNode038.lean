/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode037
import Proofs.RadenkovicGutmanD5Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-3]],[[0,0],[0]],[[27,-27],[-27]],[[0,0],[0]],[[-9,-72],[-72]],[[0,0],[0]],[[-501,-66],[-66]],[[0,0],[0]],[[-1542,-24],[-24]],[[0,0],[0]],[[-2268,-3],[-3]],[[0]],[[-1908]],[[0]],[[-957]],[[0]],[[-282]],[[0]],[[-45]],[[0]],[[-3]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
