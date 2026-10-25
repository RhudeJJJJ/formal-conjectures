/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode164
import Proofs.RadenkovicGutmanD43Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-82],[0]],[[0,0],[0]],[[-1222,0],[0,0]],[[0,0],[0,0]],[[-7596,0],[0,0]],[[0,0],[0,0]],[[-25510,0],[0,0]],[[0,0],[0,0]],[[-50152,0],[0,0]],[[0,0],[0,0]],[[-58440,-82],[-82,0]],[[0,0],[0,0]],[[-38484,-656],[-656,0]],[[0,0],[0,0]],[[-11574,-1804],[-1804,0]],[[0,0],[0,0]],[[378,-1968],[-1968,0]],[[0,0],[0,0]],[[810,-738],[-738,0]],[[0],[0,0]],[[0],[0,-82]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
