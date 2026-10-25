/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode062
import Proofs.RadenkovicGutmanD8Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,8]],[[0,0],[0,0]],[[72,120],[120,2]],[[0,0],[0]],[[2010,418],[418]],[[0,0],[0]],[[10694,480],[480]],[[0,0],[0]],[[25298,220],[220]],[[0,0],[0]],[[32908,40],[40]],[[0,0],[0]],[[25624,2],[2]],[[0]],[[12328]],[[0]],[[3650]],[[0]],[[636]],[[0]],[[58]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
