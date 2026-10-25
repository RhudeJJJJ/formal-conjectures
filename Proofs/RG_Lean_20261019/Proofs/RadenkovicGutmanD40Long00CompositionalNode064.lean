/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode062
import Proofs.RadenkovicGutmanD40Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,40]],[[0,0],[0,0]],[[360,600],[600,2]],[[0,0],[0]],[[9978,2018],[2018]],[[0,0],[0]],[[52198,2208],[2208]],[[0,0],[0]],[[120914,924],[924]],[[0,0],[0]],[[153100,136],[136]],[[0,0],[0]],[[114968,2],[2]],[[0]],[[52552]],[[0]],[[14402]],[[0]],[[2204]],[[0]],[[154]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
