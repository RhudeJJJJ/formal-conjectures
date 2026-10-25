/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode062
import Proofs.RadenkovicGutmanD19Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,19]],[[0,0],[0,0]],[[171,285],[285,2]],[[0,0],[0]],[[4749,968],[968]],[[0,0],[0]],[[24961,1074],[1074]],[[0,0],[0]],[[58166,462],[462]],[[0,0],[0]],[[74224,73],[73]],[[0,0],[0]],[[56336,2],[2]],[[0]],[[26155]],[[0]],[[7346]],[[0]],[[1175]],[[0]],[[91]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
