/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode037
import Proofs.RadenkovicGutmanD7Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-5]],[[0,0],[0]],[[45,-45],[-45]],[[0,0],[0]],[[-15,-120],[-120]],[[0,0],[0]],[[-835,-110],[-110]],[[0,0],[0]],[[-2570,-40],[-40]],[[0,0],[0]],[[-3780,-5],[-5]],[[0]],[[-3180]],[[0]],[[-1595]],[[0]],[[-470]],[[0]],[[-75]],[[0]],[[-5]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
