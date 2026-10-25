/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode160
import Proofs.RadenkovicGutmanD23Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-21],[0]],[[0,0],[0]],[[-311,0],[0,0]],[[0,0],[0,0]],[[-1918,0],[0,0]],[[0,0],[0,0]],[[-6375,0],[0,0]],[[0,0],[0,0]],[[-12356,0],[0,0]],[[0,0],[0,0]],[[-14100,-21],[-21,0]],[[0,0],[0,0]],[[-8962,-168],[-168,0]],[[0,0],[0,0]],[[-2447,-462],[-462,0]],[[0,0],[0,0]],[[249,-504],[-504,0]],[[0,0],[0,0]],[[225,-189],[-189,0]],[[0],[0,0]],[[0],[0,-21]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
