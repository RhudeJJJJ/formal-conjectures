/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode062
import Proofs.RadenkovicGutmanD45Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,45]],[[0,0],[0,0]],[[405,675],[675,2]],[[0,0],[0]],[[11223,2268],[2268]],[[0,0],[0]],[[58683,2478],[2478]],[[0,0],[0]],[[135854,1034],[1034]],[[0,0],[0]],[[171880,151],[151]],[[0,0],[0]],[[128928,2],[2]],[[0]],[[58837]],[[0]],[[16082]],[[0]],[[2449]],[[0]],[[169]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
