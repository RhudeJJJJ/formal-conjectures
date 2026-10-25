/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode062
import Proofs.RadenkovicGutmanD10Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,10]],[[0,0],[0,0]],[[90,150],[150,2]],[[0,0],[0]],[[2508,518],[518]],[[0,0],[0]],[[13288,588],[588]],[[0,0],[0]],[[31274,264],[264]],[[0,0],[0]],[[40420,46],[46]],[[0,0],[0]],[[31208,2],[2]],[[0]],[[14842]],[[0]],[[4322]],[[0]],[[734]],[[0]],[[64]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
