/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode037
import Proofs.RadenkovicGutmanD37Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-35]],[[0,0],[0]],[[315,-315],[-315]],[[0,0],[0]],[[-105,-840],[-840]],[[0,0],[0]],[[-5845,-770],[-770]],[[0,0],[0]],[[-17990,-280],[-280]],[[0,0],[0]],[[-26460,-35],[-35]],[[0]],[[-22260]],[[0]],[[-11165]],[[0]],[[-3290]],[[0]],[[-525]],[[0]],[[-35]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
