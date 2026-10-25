/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode119
import Proofs.RadenkovicGutmanD33Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-62],[0]],[[0,0],[0]],[[-922,0],[0,0]],[[0,0],[0,0]],[[-5716,0],[0,0]],[[0,0],[0,0]],[[-19130,0],[0,0]],[[0,0],[0,0]],[[-37432,0],[0,0]],[[0,0],[0,0]],[[-43320,-62],[-62,0]],[[0,0],[0,0]],[[-28204,-496],[-496,0]],[[0,0],[0,0]],[[-8234,-1364],[-1364,0]],[[0,0],[0,0]],[[438,-1488],[-1488,0]],[[0,0],[0,0]],[[630,-558],[-558,0]],[[0],[0,0]],[[0],[0,-62]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
