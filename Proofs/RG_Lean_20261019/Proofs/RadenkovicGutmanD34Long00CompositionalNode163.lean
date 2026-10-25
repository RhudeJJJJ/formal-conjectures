/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode160
import Proofs.RadenkovicGutmanD34Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-476,0],[0,0]],[[0,0],[0,0]],[[-2952,0],[0,0]],[[0,0],[0,0]],[[-9884,0],[0,0]],[[0,0],[0,0]],[[-19352,0],[0,0]],[[0,0],[0,0]],[[-22416,-32],[-32,0]],[[0,0],[0,0]],[[-14616,-256],[-256,0]],[[0,0],[0,0]],[[-4284,-704],[-704,0]],[[0,0],[0,0]],[[216,-768],[-768,0]],[[0,0],[0,0]],[[324,-288],[-288,0]],[[0],[0,0]],[[0],[0,-32]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
