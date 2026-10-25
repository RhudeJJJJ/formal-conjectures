/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode030
import Proofs.RadenkovicGutmanD35Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,35]],[[0,0],[0]],[[315,315],[315]],[[0,0],[0]],[[5565,840],[840]],[[0,0],[0]],[[24395,770],[770]],[[0,0],[0]],[[50050,280],[280]],[[0,0],[0]],[[57540,35],[35]],[[0]],[[39760]],[[0]],[[16835]],[[0]],[[4270]],[[0]],[[595]],[[0]],[[35]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
