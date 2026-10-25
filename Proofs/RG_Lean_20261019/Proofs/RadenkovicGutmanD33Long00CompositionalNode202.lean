/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode191
import Proofs.RadenkovicGutmanD33Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[67,0],[0,0]],[[0,0],[0,0]],[[805,0],[0,0]],[[0,0],[0,0]],[[4988,0],[0,0]],[[0,0],[0,0]],[[18145,0],[0,0]],[[0,0],[0,0]],[[40776,2],[2,0]],[[0,0],[0,0]],[[57112,49],[49,0]],[[0,0],[0,0]],[[48584,308],[308,0]],[[0,0],[0,0]],[[23319,774],[774,0]],[[0,0],[0,0]],[[5265,810],[810,0]],[[0,0],[0,0]],[[297,297],[297,2]],[[0],[0,0]],[[0],[0,33]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
