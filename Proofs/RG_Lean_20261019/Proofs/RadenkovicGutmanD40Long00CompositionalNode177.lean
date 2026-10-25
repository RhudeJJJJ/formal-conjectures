/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode174
import Proofs.RadenkovicGutmanD40Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-76],[0]],[[0,0],[0]],[[-1292,0],[0,0]],[[0,0],[0,0]],[[-9272,0],[0,0]],[[0,0],[0,0]],[[-36556,0],[0,0]],[[0,0],[0,0]],[[-86336,0],[0,0]],[[0,0],[0,0]],[[-124944,-76],[-76,0]],[[0,0],[0,0]],[[-108680,-608],[-608,0]],[[0,0],[0,0]],[[-52972,-1672],[-1672,0]],[[0,0],[0,0]],[[-12084,-1824],[-1824,0]],[[0,0],[0,0]],[[-684,-684],[-684,0]],[[0],[0,0]],[[0],[0,-76]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
