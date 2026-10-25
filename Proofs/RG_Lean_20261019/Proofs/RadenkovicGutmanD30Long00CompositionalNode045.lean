/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode044
import Proofs.RadenkovicGutmanD30Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,30]],[[0,0],[0,0]],[[-270,270],[270,2]],[[0,0],[0]],[[72,738],[738]],[[0,0],[0]],[[5016,708],[708]],[[0,0],[0]],[[15754,284],[284]],[[0,0],[0]],[[23708,46],[46]],[[0,0],[0]],[[20592,2],[2]],[[0]],[[10842]],[[0]],[[3458]],[[0]],[[638]],[[0]],[[60]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
