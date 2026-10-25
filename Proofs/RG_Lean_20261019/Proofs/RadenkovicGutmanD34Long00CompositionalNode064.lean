/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode062
import Proofs.RadenkovicGutmanD34Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,34]],[[0,0],[0,0]],[[306,510],[510,2]],[[0,0],[0]],[[8484,1718],[1718]],[[0,0],[0]],[[44416,1884],[1884]],[[0,0],[0]],[[102986,792],[792]],[[0,0],[0]],[[130564,118],[118]],[[0,0],[0]],[[98216,2],[2]],[[0]],[[45010]],[[0]],[[12386]],[[0]],[[1910]],[[0]],[[136]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
