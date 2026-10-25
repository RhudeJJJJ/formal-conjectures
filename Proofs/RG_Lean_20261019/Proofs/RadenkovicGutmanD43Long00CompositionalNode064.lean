/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode062
import Proofs.RadenkovicGutmanD43Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,43]],[[0,0],[0,0]],[[387,645],[645,2]],[[0,0],[0]],[[10725,2168],[2168]],[[0,0],[0]],[[56089,2370],[2370]],[[0,0],[0]],[[129878,990],[990]],[[0,0],[0]],[[164368,145],[145]],[[0,0],[0]],[[123344,2],[2]],[[0]],[[56323]],[[0]],[[15410]],[[0]],[[2351]],[[0]],[[163]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
