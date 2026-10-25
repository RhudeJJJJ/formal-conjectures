/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode119
import Proofs.RadenkovicGutmanD35Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-66],[0]],[[0,0],[0]],[[-982,0],[0,0]],[[0,0],[0,0]],[[-6092,0],[0,0]],[[0,0],[0,0]],[[-20406,0],[0,0]],[[0,0],[0,0]],[[-39976,0],[0,0]],[[0,0],[0,0]],[[-46344,-66],[-66,0]],[[0,0],[0,0]],[[-30260,-528],[-528,0]],[[0,0],[0,0]],[[-8902,-1452],[-1452,0]],[[0,0],[0,0]],[[426,-1584],[-1584,0]],[[0,0],[0,0]],[[666,-594],[-594,0]],[[0],[0,0]],[[0],[0,-66]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
