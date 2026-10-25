/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode044
import Proofs.RadenkovicGutmanD24Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,24]],[[0,0],[0,0]],[[-216,216],[216,2]],[[0,0],[0]],[[54,594],[594]],[[0,0],[0]],[[4014,576],[576]],[[0,0],[0]],[[12670,236],[236]],[[0,0],[0]],[[19172,40],[40]],[[0,0],[0]],[[16776,2],[2]],[[0]],[[8928]],[[0]],[[2894]],[[0]],[[548]],[[0]],[[54]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
