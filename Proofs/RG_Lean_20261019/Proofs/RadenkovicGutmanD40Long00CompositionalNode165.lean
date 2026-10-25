/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode164
import Proofs.RadenkovicGutmanD40Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-76],[0]],[[0,0],[0]],[[-1132,0],[0,0]],[[0,0],[0,0]],[[-7032,0],[0,0]],[[0,0],[0,0]],[[-23596,0],[0,0]],[[0,0],[0,0]],[[-46336,0],[0,0]],[[0,0],[0,0]],[[-53904,-76],[-76,0]],[[0,0],[0,0]],[[-35400,-608],[-608,0]],[[0,0],[0,0]],[[-10572,-1672],[-1672,0]],[[0,0],[0,0]],[[396,-1824],[-1824,0]],[[0,0],[0,0]],[[756,-684],[-684,0]],[[0],[0,0]],[[0],[0,-76]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
