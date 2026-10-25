/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode062
import Proofs.RadenkovicGutmanD6Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,6]],[[0,0],[0,0]],[[54,90],[90,2]],[[0,0],[0]],[[1512,318],[318]],[[0,0],[0]],[[8100,372],[372]],[[0,0],[0]],[[19322,176],[176]],[[0,0],[0]],[[25396,34],[34]],[[0,0],[0]],[[20040,2],[2]],[[0]],[[9814]],[[0]],[[2978]],[[0]],[[538]],[[0]],[[52]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
