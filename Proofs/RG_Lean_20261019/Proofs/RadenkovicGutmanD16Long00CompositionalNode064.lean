/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode062
import Proofs.RadenkovicGutmanD16Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,16]],[[0,0],[0,0]],[[144,240],[240,2]],[[0,0],[0]],[[4002,818],[818]],[[0,0],[0]],[[21070,912],[912]],[[0,0],[0]],[[49202,396],[396]],[[0,0],[0]],[[62956,64],[64]],[[0,0],[0]],[[47960,2],[2]],[[0]],[[22384]],[[0]],[[6338]],[[0]],[[1028]],[[0]],[[82]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
