/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode160
import Proofs.RadenkovicGutmanD38Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-536,0],[0,0]],[[0,0],[0,0]],[[-3328,0],[0,0]],[[0,0],[0,0]],[[-11160,0],[0,0]],[[0,0],[0,0]],[[-21896,0],[0,0]],[[0,0],[0,0]],[[-25440,-36],[-36,0]],[[0,0],[0,0]],[[-16672,-288],[-288,0]],[[0,0],[0,0]],[[-4952,-792],[-792,0]],[[0,0],[0,0]],[[204,-864],[-864,0]],[[0,0],[0,0]],[[360,-324],[-324,0]],[[0],[0,0]],[[0],[0,-36]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
