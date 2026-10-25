/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode191
import Proofs.RadenkovicGutmanD29Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[59,0],[0,0]],[[0,0],[0,0]],[[623,0],[0,0]],[[0,0],[0,0]],[[3364,0],[0,0]],[[0,0],[0,0]],[[10523,0],[0,0]],[[0,0],[0,0]],[[19956,2],[2,0]],[[0,0],[0,0]],[[22952,45],[45,0]],[[0,0],[0,0]],[[15240,276],[276,0]],[[0,0],[0,0]],[[4849,686],[686,0]],[[0,0],[0,0]],[[69,714],[714,0]],[[0,0],[0,0]],[[-261,261],[261,2]],[[0],[0,0]],[[0],[0,29]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
