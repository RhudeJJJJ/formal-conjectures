/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode062
import Proofs.RadenkovicGutmanD27Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,27]],[[0,0],[0,0]],[[243,405],[405,2]],[[0,0],[0]],[[6741,1368],[1368]],[[0,0],[0]],[[35337,1506],[1506]],[[0,0],[0]],[[82070,638],[638]],[[0,0],[0]],[[104272,97],[97]],[[0,0],[0]],[[78672,2],[2]],[[0]],[[36211]],[[0]],[[10034]],[[0]],[[1567]],[[0]],[[115]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
