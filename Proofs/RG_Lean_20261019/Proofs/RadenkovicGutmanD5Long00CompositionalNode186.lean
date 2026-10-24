/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode178
import Proofs.RadenkovicGutmanD5Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-97,0],[0,0]],[[0,0],[0,0]],[[-652,0],[0,0]],[[0,0],[0,0]],[[-2351,0],[0,0]],[[0,0],[0,0]],[[-4876,0],[0,0]],[[0,0],[0,0]],[[-5724,-6],[-6,0]],[[0,0],[0,0]],[[-3300,-43],[-43,0]],[[0,0],[0,0]],[[-287,-97],[-97,0]],[[0,0],[0,0]],[[546,-64],[-64,0]],[[0,0],[0,0]],[[171,11],[11,0]],[[0,0],[0,0]],[[0,15],[15,-6]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
