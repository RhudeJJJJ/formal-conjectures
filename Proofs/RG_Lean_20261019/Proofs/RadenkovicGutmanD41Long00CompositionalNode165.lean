/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode164
import Proofs.RadenkovicGutmanD41Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-78],[0]],[[0,0],[0]],[[-1162,0],[0,0]],[[0,0],[0,0]],[[-7220,0],[0,0]],[[0,0],[0,0]],[[-24234,0],[0,0]],[[0,0],[0,0]],[[-47608,0],[0,0]],[[0,0],[0,0]],[[-55416,-78],[-78,0]],[[0,0],[0,0]],[[-36428,-624],[-624,0]],[[0,0],[0,0]],[[-10906,-1716],[-1716,0]],[[0,0],[0,0]],[[390,-1872],[-1872,0]],[[0,0],[0,0]],[[774,-702],[-702,0]],[[0],[0,0]],[[0],[0,-78]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
