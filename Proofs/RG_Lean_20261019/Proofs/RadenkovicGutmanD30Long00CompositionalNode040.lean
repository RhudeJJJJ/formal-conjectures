/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode038
import Proofs.RadenkovicGutmanD30Long00CompositionalNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .plus e038 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[0],[0,-28]],[[0,0],[0]],[[288,-252],[-252]],[[0,0],[0]],[[228,-672],[-672]],[[0,0],[0]],[[-3616,-616],[-616]],[[0,0],[0]],[[-12560,-224],[-224]],[[0,0],[0]],[[-19392,-28],[-28]],[[0]],[[-16808]],[[0]],[[-8608]],[[0]],[[-2576]],[[0]],[[-416]],[[0]],[[-28]]]
theorem step040 : p040=NestedHorner.add p038 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_plus e040 e038 e039 p038 p039 p040 rfl h038 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
