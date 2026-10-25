/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode160
import Proofs.RadenkovicGutmanD36Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-506,0],[0,0]],[[0,0],[0,0]],[[-3140,0],[0,0]],[[0,0],[0,0]],[[-10522,0],[0,0]],[[0,0],[0,0]],[[-20624,0],[0,0]],[[0,0],[0,0]],[[-23928,-34],[-34,0]],[[0,0],[0,0]],[[-15644,-272],[-272,0]],[[0,0],[0,0]],[[-4618,-748],[-748,0]],[[0,0],[0,0]],[[210,-816],[-816,0]],[[0,0],[0,0]],[[342,-306],[-306,0]],[[0],[0,0]],[[0],[0,-34]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
