/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode073
import Proofs.RadenkovicGutmanD16Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1152,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10368,-65664,0],[-65664,-19488,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1188000,-921888,0],[-921888,-116288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17666208,-5539392,0],[-5539392,-338464,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-123470592,-18829280,0],[-18829280,-540480,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-518424608,-40444736,0],[-40444736,-500864,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1455036768,-58198880,0],[-58198880,-274368],[0]],[[0,0,0],[0,0],[0]],[[-2895749824,-58015872,0],[-58015872,-87328],[0]],[[0,0,0],[0,0],[0]],[[-4237706496,-40789824,0],[-40789824,-14912],[0]],[[0,0,0],[0,0],[0]],[[-4667616992,-20339968,0],[-20339968,-1056],[0]],[[0,0,0],[0,0],[0]],[[-3926406848,-7143008,0],[-7143008,0],[0]],[[0,0],[0]],[[-2542827200,-1725760],[-1725760]],[[0,0],[0]],[[-1270764928,-272864],[-272864]],[[0,0],[0]],[[-488371680,-25408],[-25408]],[[0,0],[0]],[[-142880736,-1056],[-1056]],[[0,0],[0]],[[-31220160,0],[0]],[[0]],[[-4929920]],[[0]],[[-531104]],[[0]],[[-34912]],[[0]],[[-1056]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
