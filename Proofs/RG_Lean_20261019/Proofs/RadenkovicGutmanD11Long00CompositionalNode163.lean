/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode160
import Proofs.RadenkovicGutmanD11Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-9],[0]],[[0,0],[0]],[[-131,0],[0,0]],[[0,0],[0,0]],[[-790,0],[0,0]],[[0,0],[0,0]],[[-2547,0],[0,0]],[[0,0],[0,0]],[[-4724,0],[0,0]],[[0,0],[0,0]],[[-5028,-9],[-9,0]],[[0,0],[0,0]],[[-2794,-72],[-72,0]],[[0,0],[0,0]],[[-443,-198],[-198,0]],[[0,0],[0,0]],[[285,-216],[-216,0]],[[0,0],[0,0]],[[117,-81],[-81,0]],[[0],[0,0]],[[0],[0,-9]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
