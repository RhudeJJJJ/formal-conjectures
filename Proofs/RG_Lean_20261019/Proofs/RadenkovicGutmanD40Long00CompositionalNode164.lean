/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode119
import Proofs.RadenkovicGutmanD40Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-76],[0]],[[0,0],[0]],[[-1132,0],[0,0]],[[0,0],[0,0]],[[-7032,0],[0,0]],[[0,0],[0,0]],[[-23596,0],[0,0]],[[0,0],[0,0]],[[-46336,0],[0,0]],[[0,0],[0,0]],[[-53904,-76],[-76,0]],[[0,0],[0,0]],[[-35400,-608],[-608,0]],[[0,0],[0,0]],[[-10572,-1672],[-1672,0]],[[0,0],[0,0]],[[396,-1824],[-1824,0]],[[0,0],[0,0]],[[756,-684],[-684,0]],[[0],[0,0]],[[0],[0,-76]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
