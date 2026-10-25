/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode160
import Proofs.RadenkovicGutmanD18Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-236,0],[0,0]],[[0,0],[0,0]],[[-1448,0],[0,0]],[[0,0],[0,0]],[[-4780,0],[0,0]],[[0,0],[0,0]],[[-9176,0],[0,0]],[[0,0],[0,0]],[[-10320,-16],[-16,0]],[[0,0],[0,0]],[[-6392,-128],[-128,0]],[[0,0],[0,0]],[[-1612,-352],[-352,0]],[[0,0],[0,0]],[[264,-384],[-384,0]],[[0,0],[0,0]],[[180,-144],[-144,0]],[[0],[0,0]],[[0],[0,-16]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
