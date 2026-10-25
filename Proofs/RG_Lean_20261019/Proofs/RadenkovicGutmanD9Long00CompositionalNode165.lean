/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode164
import Proofs.RadenkovicGutmanD9Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-202,0],[0,0]],[[0,0],[0,0]],[[-1204,0],[0,0]],[[0,0],[0,0]],[[-3818,0],[0,0]],[[0,0],[0,0]],[[-6904,0],[0,0]],[[0,0],[0,0]],[[-7032,-14],[-14,0]],[[0,0],[0,0]],[[-3532,-112],[-112,0]],[[0,0],[0,0]],[[-218,-308],[-308,0]],[[0,0],[0,0]],[[582,-336],[-336,0]],[[0,0],[0,0]],[[198,-126],[-126,0]],[[0],[0,0]],[[0],[0,-14]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
