/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode037
import Proofs.RadenkovicGutmanD25Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-23]],[[0,0],[0]],[[207,-207],[-207]],[[0,0],[0]],[[-69,-552],[-552]],[[0,0],[0]],[[-3841,-506],[-506]],[[0,0],[0]],[[-11822,-184],[-184]],[[0,0],[0]],[[-17388,-23],[-23]],[[0]],[[-14628]],[[0]],[[-7337]],[[0]],[[-2162]],[[0]],[[-345]],[[0]],[[-23]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
