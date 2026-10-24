/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode160
import Proofs.RadenkovicGutmanD5Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-3],[0]],[[0,0],[0]],[[-41,0],[0,0]],[[0,0],[0,0]],[[-226,0],[0,0]],[[0,0],[0,0]],[[-633,0],[0,0]],[[0,0],[0,0]],[[-908,0],[0,0]],[[0,0],[0,0]],[[-492,-3],[-3,0]],[[0,0],[0,0]],[[290,-24],[-24,0]],[[0,0],[0,0]],[[559,-66],[-66,0]],[[0,0],[0,0]],[[303,-72],[-72,0]],[[0,0],[0,0]],[[63,-27],[-27,0]],[[0],[0,0]],[[0],[0,-3]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
