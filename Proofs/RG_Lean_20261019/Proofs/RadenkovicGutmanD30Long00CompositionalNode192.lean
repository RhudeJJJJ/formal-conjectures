/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode191
import Proofs.RadenkovicGutmanD30Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[60,0],[0,0]],[[0,0],[0,0]],[[638,0],[0,0]],[[0,0],[0,0]],[[3458,0],[0,0]],[[0,0],[0,0]],[[10842,0],[0,0]],[[0,0],[0,0]],[[20592,2],[2,0]],[[0,0],[0,0]],[[23708,46],[46,0]],[[0,0],[0,0]],[[15754,284],[284,0]],[[0,0],[0,0]],[[5016,708],[708,0]],[[0,0],[0,0]],[[72,738],[738,0]],[[0,0],[0,0]],[[-270,270],[270,2]],[[0],[0,0]],[[0],[0,30]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
