/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode037
import Proofs.RadenkovicGutmanD23Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-21]],[[0,0],[0]],[[189,-189],[-189]],[[0,0],[0]],[[-63,-504],[-504]],[[0,0],[0]],[[-3507,-462],[-462]],[[0,0],[0]],[[-10794,-168],[-168]],[[0,0],[0]],[[-15876,-21],[-21]],[[0]],[[-13356]],[[0]],[[-6699]],[[0]],[[-1974]],[[0]],[[-315]],[[0]],[[-21]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
