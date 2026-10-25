/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode119
import Proofs.RadenkovicGutmanD43Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-82],[0]],[[0,0],[0]],[[-1222,0],[0,0]],[[0,0],[0,0]],[[-7596,0],[0,0]],[[0,0],[0,0]],[[-25510,0],[0,0]],[[0,0],[0,0]],[[-50152,0],[0,0]],[[0,0],[0,0]],[[-58440,-82],[-82,0]],[[0,0],[0,0]],[[-38484,-656],[-656,0]],[[0,0],[0,0]],[[-11574,-1804],[-1804,0]],[[0,0],[0,0]],[[378,-1968],[-1968,0]],[[0,0],[0,0]],[[810,-738],[-738,0]],[[0],[0,0]],[[0],[0,-82]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
