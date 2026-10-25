/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode062
import Proofs.RadenkovicGutmanD22Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,22]],[[0,0],[0,0]],[[198,330],[330,2]],[[0,0],[0]],[[5496,1118],[1118]],[[0,0],[0]],[[28852,1236],[1236]],[[0,0],[0]],[[67130,528],[528]],[[0,0],[0]],[[85492,82],[82]],[[0,0],[0]],[[64712,2],[2]],[[0]],[[29926]],[[0]],[[8354]],[[0]],[[1322]],[[0]],[[100]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
