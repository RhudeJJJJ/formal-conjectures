/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode044
import Proofs.RadenkovicGutmanD22Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,22]],[[0,0],[0,0]],[[-198,198],[198,2]],[[0,0],[0]],[[48,546],[546]],[[0,0],[0]],[[3680,532],[532]],[[0,0],[0]],[[11642,220],[220]],[[0,0],[0]],[[17660,38],[38]],[[0,0],[0]],[[15504,2],[2]],[[0]],[[8290]],[[0]],[[2706]],[[0]],[[518]],[[0]],[[52]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
