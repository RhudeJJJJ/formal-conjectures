/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode202
import Proofs.RadenkovicGutmanD33Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[67,0],[0,0]],[[0,0],[0,0]],[[805,0],[0,0]],[[0,0],[0,0]],[[4988,0],[0,0]],[[0,0],[0,0]],[[18145,0],[0,0]],[[0,0],[0,0]],[[40776,2],[2,0]],[[0,0],[0,0]],[[57112,49],[49,0]],[[0,0],[0,0]],[[48584,308],[308,0]],[[0,0],[0,0]],[[23319,774],[774,0]],[[0,0],[0,0]],[[5265,810],[810,0]],[[0,0],[0,0]],[[297,297],[297,2]],[[0],[0,0]],[[0],[0,33]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
