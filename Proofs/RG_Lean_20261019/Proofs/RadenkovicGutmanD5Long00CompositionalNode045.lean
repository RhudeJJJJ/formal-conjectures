/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode044
import Proofs.RadenkovicGutmanD5Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,5]],[[0,0],[0,0]],[[-45,45],[45,2]],[[0,0],[0]],[[-3,138],[138]],[[0,0],[0]],[[841,158],[158]],[[0,0],[0]],[[2904,84],[84]],[[0,0],[0]],[[4808,21],[21]],[[0,0],[0]],[[4692,2],[2]],[[0]],[[2867]],[[0]],[[1108]],[[0]],[[263]],[[0]],[[35]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
