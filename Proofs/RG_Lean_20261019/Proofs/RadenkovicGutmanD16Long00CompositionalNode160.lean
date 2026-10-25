/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode159
import Proofs.RadenkovicGutmanD16Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-210,0],[0,0]],[[0,0],[0,0]],[[-1316,0],[0,0]],[[0,0],[0,0]],[[-4466,0],[0,0]],[[0,0],[0,0]],[[-8904,0],[0,0]],[[0,0],[0,0]],[[-10584,-14],[-14,0]],[[0,0],[0,0]],[[-7196,-112],[-112,0]],[[0,0],[0,0]],[[-2338,-308],[-308,0]],[[0,0],[0,0]],[[-42,-336],[-336,0]],[[0,0],[0,0]],[[126,-126],[-126,0]],[[0],[0,0]],[[0],[0,-14]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
