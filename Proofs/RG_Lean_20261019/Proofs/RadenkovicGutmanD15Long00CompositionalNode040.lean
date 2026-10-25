/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode038
import Proofs.RadenkovicGutmanD15Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-13]],[[0,0],[0]],[[153,-117],[-117]],[[0,0],[0]],[[273,-312],[-312]],[[0,0],[0]],[[-1111,-286],[-286]],[[0,0],[0]],[[-4850,-104],[-104]],[[0,0],[0]],[[-8052,-13],[-13]],[[0]],[[-7268]],[[0]],[[-3823]],[[0]],[[-1166]],[[0]],[[-191]],[[0]],[[-13]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
