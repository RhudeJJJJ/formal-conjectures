/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode192
import Proofs.RadenkovicGutmanD37Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[67,0],[0,0]],[[0,0],[0,0]],[[743,0],[0,0]],[[0,0],[0,0]],[[4116,0],[0,0]],[[0,0],[0,0]],[[13075,0],[0,0]],[[0,0],[0,0]],[[25044,2],[2,0]],[[0,0],[0,0]],[[29000,53],[53,0]],[[0,0],[0,0]],[[19352,340],[340,0]],[[0,0],[0,0]],[[6185,862],[862,0]],[[0,0],[0,0]],[[93,906],[906,0]],[[0,0],[0,0]],[[-333,333],[333,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
