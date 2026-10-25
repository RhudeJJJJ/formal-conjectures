/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode044
import Proofs.RadenkovicGutmanD37Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,37]],[[0,0],[0,0]],[[-333,333],[333,2]],[[0,0],[0]],[[93,906],[906]],[[0,0],[0]],[[6185,862],[862]],[[0,0],[0]],[[19352,340],[340]],[[0,0],[0]],[[29000,53],[53]],[[0,0],[0]],[[25044,2],[2]],[[0]],[[13075]],[[0]],[[4116]],[[0]],[[743]],[[0]],[[67]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
