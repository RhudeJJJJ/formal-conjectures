/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode164
import Proofs.RadenkovicGutmanD45Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-86],[0]],[[0,0],[0]],[[-1282,0],[0,0]],[[0,0],[0,0]],[[-7972,0],[0,0]],[[0,0],[0,0]],[[-26786,0],[0,0]],[[0,0],[0,0]],[[-52696,0],[0,0]],[[0,0],[0,0]],[[-61464,-86],[-86,0]],[[0,0],[0,0]],[[-40540,-688],[-688,0]],[[0,0],[0,0]],[[-12242,-1892],[-1892,0]],[[0,0],[0,0]],[[366,-2064],[-2064,0]],[[0,0],[0,0]],[[846,-774],[-774,0]],[[0],[0,0]],[[0],[0,-86]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
