/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode044
import Proofs.RadenkovicGutmanD29Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,29]],[[0,0],[0,0]],[[-261,261],[261,2]],[[0,0],[0]],[[69,714],[714]],[[0,0],[0]],[[4849,686],[686]],[[0,0],[0]],[[15240,276],[276]],[[0,0],[0]],[[22952,45],[45]],[[0,0],[0]],[[19956,2],[2]],[[0]],[[10523]],[[0]],[[3364]],[[0]],[[623]],[[0]],[[59]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
