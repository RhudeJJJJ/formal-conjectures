/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode044
import Proofs.RadenkovicGutmanD17Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,17]],[[0,0],[0,0]],[[-153,153],[153,2]],[[0,0],[0]],[[33,426],[426]],[[0,0],[0]],[[2845,422],[422]],[[0,0],[0]],[[9072,180],[180]],[[0,0],[0]],[[13880,33],[33]],[[0,0],[0]],[[12324,2],[2]],[[0]],[[6695]],[[0]],[[2236]],[[0]],[[443]],[[0]],[[47]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
