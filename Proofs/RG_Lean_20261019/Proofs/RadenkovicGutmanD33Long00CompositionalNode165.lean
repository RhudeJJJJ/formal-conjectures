/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode164
import Proofs.RadenkovicGutmanD33Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-62],[0]],[[0,0],[0]],[[-922,0],[0,0]],[[0,0],[0,0]],[[-5716,0],[0,0]],[[0,0],[0,0]],[[-19130,0],[0,0]],[[0,0],[0,0]],[[-37432,0],[0,0]],[[0,0],[0,0]],[[-43320,-62],[-62,0]],[[0,0],[0,0]],[[-28204,-496],[-496,0]],[[0,0],[0,0]],[[-8234,-1364],[-1364,0]],[[0,0],[0,0]],[[438,-1488],[-1488,0]],[[0,0],[0,0]],[[630,-558],[-558,0]],[[0],[0,0]],[[0],[0,-62]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
