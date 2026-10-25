/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode164
import Proofs.RadenkovicGutmanD21Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-38],[0]],[[0,0],[0]],[[-562,0],[0,0]],[[0,0],[0,0]],[[-3460,0],[0,0]],[[0,0],[0,0]],[[-11474,0],[0,0]],[[0,0],[0,0]],[[-22168,0],[0,0]],[[0,0],[0,0]],[[-25176,-38],[-38,0]],[[0,0],[0,0]],[[-15868,-304],[-304,0]],[[0,0],[0,0]],[[-4226,-836],[-836,0]],[[0,0],[0,0]],[[510,-912],[-912,0]],[[0,0],[0,0]],[[414,-342],[-342,0]],[[0],[0,0]],[[0],[0,-38]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
