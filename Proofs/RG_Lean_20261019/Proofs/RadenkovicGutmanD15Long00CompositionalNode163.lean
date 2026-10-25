/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode160
import Proofs.RadenkovicGutmanD15Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-13],[0]],[[0,0],[0]],[[-191,0],[0,0]],[[0,0],[0,0]],[[-1166,0],[0,0]],[[0,0],[0,0]],[[-3823,0],[0,0]],[[0,0],[0,0]],[[-7268,0],[0,0]],[[0,0],[0,0]],[[-8052,-13],[-13,0]],[[0,0],[0,0]],[[-4850,-104],[-104,0]],[[0,0],[0,0]],[[-1111,-286],[-286,0]],[[0,0],[0,0]],[[273,-312],[-312,0]],[[0,0],[0,0]],[[153,-117],[-117,0]],[[0],[0,0]],[[0],[0,-13]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
