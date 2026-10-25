/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode044
import Proofs.RadenkovicGutmanD23Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,23]],[[0,0],[0,0]],[[-207,207],[207,2]],[[0,0],[0]],[[51,570],[570]],[[0,0],[0]],[[3847,554],[554]],[[0,0],[0]],[[12156,228],[228]],[[0,0],[0]],[[18416,39],[39]],[[0,0],[0]],[[16140,2],[2]],[[0]],[[8609]],[[0]],[[2800]],[[0]],[[533]],[[0]],[[53]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
