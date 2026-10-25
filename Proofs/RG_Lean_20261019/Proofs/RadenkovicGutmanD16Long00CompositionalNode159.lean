/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode037
import Proofs.RadenkovicGutmanD16Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-210,0],[0,0]],[[0,0],[0,0]],[[-1316,0],[0,0]],[[0,0],[0,0]],[[-4466,0],[0,0]],[[0,0],[0,0]],[[-8904,0],[0,0]],[[0,0],[0,0]],[[-10584,-14],[-14,0]],[[0,0],[0,0]],[[-7196,-112],[-112,0]],[[0,0],[0,0]],[[-2338,-308],[-308,0]],[[0,0],[0,0]],[[-42,-336],[-336,0]],[[0,0],[0,0]],[[126,-126],[-126,0]],[[0],[0,0]],[[0],[0,-14]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
