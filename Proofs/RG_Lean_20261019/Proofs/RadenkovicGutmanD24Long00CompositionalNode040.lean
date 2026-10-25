/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode038
import Proofs.RadenkovicGutmanD24Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-22]],[[0,0],[0]],[[234,-198],[-198]],[[0,0],[0]],[[246,-528],[-528]],[[0,0],[0]],[[-2614,-484],[-484]],[[0,0],[0]],[[-9476,-176],[-176]],[[0,0],[0]],[[-14856,-22],[-22]],[[0]],[[-12992]],[[0]],[[-6694]],[[0]],[[-2012]],[[0]],[[-326]],[[0]],[[-22]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
