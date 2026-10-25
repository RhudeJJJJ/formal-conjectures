/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode062
import Proofs.RadenkovicGutmanD33Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,33]],[[0,0],[0,0]],[[297,495],[495,2]],[[0,0],[0]],[[8235,1668],[1668]],[[0,0],[0]],[[43119,1830],[1830]],[[0,0],[0]],[[99998,770],[770]],[[0,0],[0]],[[126808,115],[115]],[[0,0],[0]],[[95424,2],[2]],[[0]],[[43753]],[[0]],[[12050]],[[0]],[[1861]],[[0]],[[133]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
