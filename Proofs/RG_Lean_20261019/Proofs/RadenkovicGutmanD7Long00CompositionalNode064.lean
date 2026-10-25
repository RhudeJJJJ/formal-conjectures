/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode062
import Proofs.RadenkovicGutmanD7Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,7]],[[0,0],[0,0]],[[63,105],[105,2]],[[0,0],[0]],[[1761,368],[368]],[[0,0],[0]],[[9397,426],[426]],[[0,0],[0]],[[22310,198],[198]],[[0,0],[0]],[[29152,37],[37]],[[0,0],[0]],[[22832,2],[2]],[[0]],[[11071]],[[0]],[[3314]],[[0]],[[587]],[[0]],[[55]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
