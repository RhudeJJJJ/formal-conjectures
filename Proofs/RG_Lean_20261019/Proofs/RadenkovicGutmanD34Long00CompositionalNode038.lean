/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode037
import Proofs.RadenkovicGutmanD34Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-32]],[[0,0],[0]],[[288,-288],[-288]],[[0,0],[0]],[[-96,-768],[-768]],[[0,0],[0]],[[-5344,-704],[-704]],[[0,0],[0]],[[-16448,-256],[-256]],[[0,0],[0]],[[-24192,-32],[-32]],[[0]],[[-20352]],[[0]],[[-10208]],[[0]],[[-3008]],[[0]],[[-480]],[[0]],[[-32]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
