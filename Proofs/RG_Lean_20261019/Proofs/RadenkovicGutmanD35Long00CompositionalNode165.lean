/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode164
import Proofs.RadenkovicGutmanD35Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-66],[0]],[[0,0],[0]],[[-982,0],[0,0]],[[0,0],[0,0]],[[-6092,0],[0,0]],[[0,0],[0,0]],[[-20406,0],[0,0]],[[0,0],[0,0]],[[-39976,0],[0,0]],[[0,0],[0,0]],[[-46344,-66],[-66,0]],[[0,0],[0,0]],[[-30260,-528],[-528,0]],[[0,0],[0,0]],[[-8902,-1452],[-1452,0]],[[0,0],[0,0]],[[426,-1584],[-1584,0]],[[0,0],[0,0]],[[666,-594],[-594,0]],[[0],[0,0]],[[0],[0,-66]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
