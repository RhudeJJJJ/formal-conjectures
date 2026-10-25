/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode160
import Proofs.RadenkovicGutmanD22Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-296,0],[0,0]],[[0,0],[0,0]],[[-1824,0],[0,0]],[[0,0],[0,0]],[[-6056,0],[0,0]],[[0,0],[0,0]],[[-11720,0],[0,0]],[[0,0],[0,0]],[[-13344,-20],[-20,0]],[[0,0],[0,0]],[[-8448,-160],[-160,0]],[[0,0],[0,0]],[[-2280,-440],[-440,0]],[[0,0],[0,0]],[[252,-480],[-480,0]],[[0,0],[0,0]],[[216,-180],[-180,0]],[[0],[0,0]],[[0],[0,-20]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
