/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode044
import Proofs.RadenkovicGutmanD41Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,41]],[[0,0],[0,0]],[[-369,369],[369,2]],[[0,0],[0]],[[105,1002],[1002]],[[0,0],[0]],[[6853,950],[950]],[[0,0],[0]],[[21408,372],[372]],[[0,0],[0]],[[32024,57],[57]],[[0,0],[0]],[[27588,2],[2]],[[0]],[[14351]],[[0]],[[4492]],[[0]],[[803]],[[0]],[[71]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
