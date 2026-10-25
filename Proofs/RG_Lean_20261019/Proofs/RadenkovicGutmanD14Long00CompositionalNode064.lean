/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode062
import Proofs.RadenkovicGutmanD14Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,14]],[[0,0],[0,0]],[[126,210],[210,2]],[[0,0],[0]],[[3504,718],[718]],[[0,0],[0]],[[18476,804],[804]],[[0,0],[0]],[[43226,352],[352]],[[0,0],[0]],[[55444,58],[58]],[[0,0],[0]],[[42376,2],[2]],[[0]],[[19870]],[[0]],[[5666]],[[0]],[[930]],[[0]],[[76]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
