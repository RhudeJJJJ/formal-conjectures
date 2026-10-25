/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode062
import Proofs.RadenkovicGutmanD38Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,38]],[[0,0],[0,0]],[[342,570],[570,2]],[[0,0],[0]],[[9480,1918],[1918]],[[0,0],[0]],[[49604,2100],[2100]],[[0,0],[0]],[[114938,880],[880]],[[0,0],[0]],[[145588,130],[130]],[[0,0],[0]],[[109384,2],[2]],[[0]],[[50038]],[[0]],[[13730]],[[0]],[[2106]],[[0]],[[148]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
