/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode160
import Proofs.RadenkovicGutmanD19Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-17],[0]],[[0,0],[0]],[[-251,0],[0,0]],[[0,0],[0,0]],[[-1542,0],[0,0]],[[0,0],[0,0]],[[-5099,0],[0,0]],[[0,0],[0,0]],[[-9812,0],[0,0]],[[0,0],[0,0]],[[-11076,-17],[-17,0]],[[0,0],[0,0]],[[-6906,-136],[-136,0]],[[0,0],[0,0]],[[-1779,-374],[-374,0]],[[0,0],[0,0]],[[261,-408],[-408,0]],[[0,0],[0,0]],[[189,-153],[-153,0]],[[0],[0,0]],[[0],[0,-17]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
