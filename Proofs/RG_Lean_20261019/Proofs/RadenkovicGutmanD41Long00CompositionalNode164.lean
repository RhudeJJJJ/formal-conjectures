/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode119
import Proofs.RadenkovicGutmanD41Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-78],[0]],[[0,0],[0]],[[-1162,0],[0,0]],[[0,0],[0,0]],[[-7220,0],[0,0]],[[0,0],[0,0]],[[-24234,0],[0,0]],[[0,0],[0,0]],[[-47608,0],[0,0]],[[0,0],[0,0]],[[-55416,-78],[-78,0]],[[0,0],[0,0]],[[-36428,-624],[-624,0]],[[0,0],[0,0]],[[-10906,-1716],[-1716,0]],[[0,0],[0,0]],[[390,-1872],[-1872,0]],[[0,0],[0,0]],[[774,-702],[-702,0]],[[0],[0,0]],[[0],[0,-78]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
