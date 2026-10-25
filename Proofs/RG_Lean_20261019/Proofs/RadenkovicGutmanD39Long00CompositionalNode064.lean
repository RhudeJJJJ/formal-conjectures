/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode062
import Proofs.RadenkovicGutmanD39Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,39]],[[0,0],[0,0]],[[351,585],[585,2]],[[0,0],[0]],[[9729,1968],[1968]],[[0,0],[0]],[[50901,2154],[2154]],[[0,0],[0]],[[117926,902],[902]],[[0,0],[0]],[[149344,133],[133]],[[0,0],[0]],[[112176,2],[2]],[[0]],[[51295]],[[0]],[[14066]],[[0]],[[2155]],[[0]],[[151]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
