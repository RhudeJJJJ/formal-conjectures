/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode192
import Proofs.RadenkovicGutmanD30Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[60,0],[0,0]],[[0,0],[0,0]],[[638,0],[0,0]],[[0,0],[0,0]],[[3458,0],[0,0]],[[0,0],[0,0]],[[10842,0],[0,0]],[[0,0],[0,0]],[[20592,2],[2,0]],[[0,0],[0,0]],[[23708,46],[46,0]],[[0,0],[0,0]],[[15754,284],[284,0]],[[0,0],[0,0]],[[5016,708],[708,0]],[[0,0],[0,0]],[[72,738],[738,0]],[[0,0],[0,0]],[[-270,270],[270,2]],[[0],[0,0]],[[0],[0,30]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
