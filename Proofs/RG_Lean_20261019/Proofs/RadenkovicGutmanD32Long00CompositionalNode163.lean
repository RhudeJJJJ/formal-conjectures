/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode160
import Proofs.RadenkovicGutmanD32Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-446,0],[0,0]],[[0,0],[0,0]],[[-2764,0],[0,0]],[[0,0],[0,0]],[[-9246,0],[0,0]],[[0,0],[0,0]],[[-18080,0],[0,0]],[[0,0],[0,0]],[[-20904,-30],[-30,0]],[[0,0],[0,0]],[[-13588,-240],[-240,0]],[[0,0],[0,0]],[[-3950,-660],[-660,0]],[[0,0],[0,0]],[[222,-720],[-720,0]],[[0,0],[0,0]],[[306,-270],[-270,0]],[[0],[0,0]],[[0],[0,-30]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
