/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode160
import Proofs.RadenkovicGutmanD33Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-31],[0]],[[0,0],[0]],[[-461,0],[0,0]],[[0,0],[0,0]],[[-2858,0],[0,0]],[[0,0],[0,0]],[[-9565,0],[0,0]],[[0,0],[0,0]],[[-18716,0],[0,0]],[[0,0],[0,0]],[[-21660,-31],[-31,0]],[[0,0],[0,0]],[[-14102,-248],[-248,0]],[[0,0],[0,0]],[[-4117,-682],[-682,0]],[[0,0],[0,0]],[[219,-744],[-744,0]],[[0,0],[0,0]],[[315,-279],[-279,0]],[[0],[0,0]],[[0],[0,-31]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
