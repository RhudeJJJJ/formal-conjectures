/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode177
import Proofs.RadenkovicGutmanD40Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-76],[0]],[[0,0],[0]],[[-1292,0],[0,0]],[[0,0],[0,0]],[[-9272,0],[0,0]],[[0,0],[0,0]],[[-36556,0],[0,0]],[[0,0],[0,0]],[[-86336,0],[0,0]],[[0,0],[0,0]],[[-124944,-76],[-76,0]],[[0,0],[0,0]],[[-108680,-608],[-608,0]],[[0,0],[0,0]],[[-52972,-1672],[-1672,0]],[[0,0],[0,0]],[[-12084,-1824],[-1824,0]],[[0,0],[0,0]],[[-684,-684],[-684,0]],[[0],[0,0]],[[0],[0,-76]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
