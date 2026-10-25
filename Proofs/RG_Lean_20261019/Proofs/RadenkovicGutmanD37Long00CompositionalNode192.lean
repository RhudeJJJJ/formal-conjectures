/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode191
import Proofs.RadenkovicGutmanD37Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[67,0],[0,0]],[[0,0],[0,0]],[[743,0],[0,0]],[[0,0],[0,0]],[[4116,0],[0,0]],[[0,0],[0,0]],[[13075,0],[0,0]],[[0,0],[0,0]],[[25044,2],[2,0]],[[0,0],[0,0]],[[29000,53],[53,0]],[[0,0],[0,0]],[[19352,340],[340,0]],[[0,0],[0,0]],[[6185,862],[862,0]],[[0,0],[0,0]],[[93,906],[906,0]],[[0,0],[0,0]],[[-333,333],[333,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
