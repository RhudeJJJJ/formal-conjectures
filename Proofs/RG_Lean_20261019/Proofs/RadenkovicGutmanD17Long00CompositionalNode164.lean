/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode119
import Proofs.RadenkovicGutmanD17Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-442,0],[0,0]],[[0,0],[0,0]],[[-2708,0],[0,0]],[[0,0],[0,0]],[[-8922,0],[0,0]],[[0,0],[0,0]],[[-17080,0],[0,0]],[[0,0],[0,0]],[[-19128,-30],[-30,0]],[[0,0],[0,0]],[[-11756,-240],[-240,0]],[[0,0],[0,0]],[[-2890,-660],[-660,0]],[[0,0],[0,0]],[[534,-720],[-720,0]],[[0,0],[0,0]],[[342,-270],[-270,0]],[[0],[0,0]],[[0],[0,-30]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
