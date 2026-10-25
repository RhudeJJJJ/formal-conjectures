/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode058
import Proofs.RadenkovicGutmanD40Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-76]],[[0,0],[0]],[[-684,-684],[-684]],[[0,0],[0]],[[-12084,-1824],[-1824]],[[0,0],[0]],[[-52972,-1672],[-1672]],[[0,0],[0]],[[-108680,-608],[-608]],[[0,0],[0]],[[-124944,-76],[-76]],[[0]],[[-86336]],[[0]],[[-36556]],[[0]],[[-9272]],[[0]],[[-1292]],[[0]],[[-76]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
