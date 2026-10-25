/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode044
import Proofs.RadenkovicGutmanD33Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,33]],[[0,0],[0,0]],[[297,297],[297,2]],[[0,0],[0]],[[5265,810],[810]],[[0,0],[0]],[[23319,774],[774]],[[0,0],[0]],[[48584,308],[308]],[[0,0],[0]],[[57112,49],[49]],[[0,0],[0]],[[40776,2],[2]],[[0]],[[18145]],[[0]],[[4988]],[[0]],[[805]],[[0]],[[67]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
