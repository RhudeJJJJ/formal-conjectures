/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode160
import Proofs.RadenkovicGutmanD24Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-326,0],[0,0]],[[0,0],[0,0]],[[-2012,0],[0,0]],[[0,0],[0,0]],[[-6694,0],[0,0]],[[0,0],[0,0]],[[-12992,0],[0,0]],[[0,0],[0,0]],[[-14856,-22],[-22,0]],[[0,0],[0,0]],[[-9476,-176],[-176,0]],[[0,0],[0,0]],[[-2614,-484],[-484,0]],[[0,0],[0,0]],[[246,-528],[-528,0]],[[0,0],[0,0]],[[234,-198],[-198,0]],[[0],[0,0]],[[0],[0,-22]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
