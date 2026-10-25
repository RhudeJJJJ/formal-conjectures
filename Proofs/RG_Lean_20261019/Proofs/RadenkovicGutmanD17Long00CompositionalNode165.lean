/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode164
import Proofs.RadenkovicGutmanD17Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-442,0],[0,0]],[[0,0],[0,0]],[[-2708,0],[0,0]],[[0,0],[0,0]],[[-8922,0],[0,0]],[[0,0],[0,0]],[[-17080,0],[0,0]],[[0,0],[0,0]],[[-19128,-30],[-30,0]],[[0,0],[0,0]],[[-11756,-240],[-240,0]],[[0,0],[0,0]],[[-2890,-660],[-660,0]],[[0,0],[0,0]],[[534,-720],[-720,0]],[[0,0],[0,0]],[[342,-270],[-270,0]],[[0],[0,0]],[[0],[0,-30]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
