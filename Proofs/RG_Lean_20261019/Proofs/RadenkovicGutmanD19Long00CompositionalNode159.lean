/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode037
import Proofs.RadenkovicGutmanD19Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-17],[0]],[[0,0],[0]],[[-255,0],[0,0]],[[0,0],[0,0]],[[-1598,0],[0,0]],[[0,0],[0,0]],[[-5423,0],[0,0]],[[0,0],[0,0]],[[-10812,0],[0,0]],[[0,0],[0,0]],[[-12852,-17],[-17,0]],[[0,0],[0,0]],[[-8738,-136],[-136,0]],[[0,0],[0,0]],[[-2839,-374],[-374,0]],[[0,0],[0,0]],[[-51,-408],[-408,0]],[[0,0],[0,0]],[[153,-153],[-153,0]],[[0],[0,0]],[[0],[0,-17]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
