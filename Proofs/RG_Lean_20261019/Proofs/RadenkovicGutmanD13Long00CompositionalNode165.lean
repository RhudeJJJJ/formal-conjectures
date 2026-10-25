/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode164
import Proofs.RadenkovicGutmanD13Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-322,0],[0,0]],[[0,0],[0,0]],[[-1956,0],[0,0]],[[0,0],[0,0]],[[-6370,0],[0,0]],[[0,0],[0,0]],[[-11992,0],[0,0]],[[0,0],[0,0]],[[-13080,-22],[-22,0]],[[0,0],[0,0]],[[-7644,-176],[-176,0]],[[0,0],[0,0]],[[-1554,-484],[-484,0]],[[0,0],[0,0]],[[558,-528],[-528,0]],[[0,0],[0,0]],[[270,-198],[-198,0]],[[0],[0,0]],[[0],[0,-22]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
