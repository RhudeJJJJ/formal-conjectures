/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode119
import Proofs.RadenkovicGutmanD9Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-202,0],[0,0]],[[0,0],[0,0]],[[-1204,0],[0,0]],[[0,0],[0,0]],[[-3818,0],[0,0]],[[0,0],[0,0]],[[-6904,0],[0,0]],[[0,0],[0,0]],[[-7032,-14],[-14,0]],[[0,0],[0,0]],[[-3532,-112],[-112,0]],[[0,0],[0,0]],[[-218,-308],[-308,0]],[[0,0],[0,0]],[[582,-336],[-336,0]],[[0,0],[0,0]],[[198,-126],[-126,0]],[[0],[0,0]],[[0],[0,-14]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
