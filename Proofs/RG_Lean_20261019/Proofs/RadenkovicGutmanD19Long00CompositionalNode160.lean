/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode159
import Proofs.RadenkovicGutmanD19Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-17],[0]],[[0,0],[0]],[[-255,0],[0,0]],[[0,0],[0,0]],[[-1598,0],[0,0]],[[0,0],[0,0]],[[-5423,0],[0,0]],[[0,0],[0,0]],[[-10812,0],[0,0]],[[0,0],[0,0]],[[-12852,-17],[-17,0]],[[0,0],[0,0]],[[-8738,-136],[-136,0]],[[0,0],[0,0]],[[-2839,-374],[-374,0]],[[0,0],[0,0]],[[-51,-408],[-408,0]],[[0,0],[0,0]],[[153,-153],[-153,0]],[[0],[0,0]],[[0],[0,-17]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
