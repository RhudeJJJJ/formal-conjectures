/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode062
import Proofs.RadenkovicGutmanD35Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,35]],[[0,0],[0,0]],[[315,525],[525,2]],[[0,0],[0]],[[8733,1768],[1768]],[[0,0],[0]],[[45713,1938],[1938]],[[0,0],[0]],[[105974,814],[814]],[[0,0],[0]],[[134320,121],[121]],[[0,0],[0]],[[101008,2],[2]],[[0]],[[46267]],[[0]],[[12722]],[[0]],[[1959]],[[0]],[[139]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
