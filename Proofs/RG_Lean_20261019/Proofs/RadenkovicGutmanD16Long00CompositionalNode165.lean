/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode164
import Proofs.RadenkovicGutmanD16Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-412,0],[0,0]],[[0,0],[0,0]],[[-2520,0],[0,0]],[[0,0],[0,0]],[[-8284,0],[0,0]],[[0,0],[0,0]],[[-15808,0],[0,0]],[[0,0],[0,0]],[[-17616,-28],[-28,0]],[[0,0],[0,0]],[[-10728,-224],[-224,0]],[[0,0],[0,0]],[[-2556,-616],[-616,0]],[[0,0],[0,0]],[[540,-672],[-672,0]],[[0,0],[0,0]],[[324,-252],[-252,0]],[[0],[0,0]],[[0],[0,-28]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
