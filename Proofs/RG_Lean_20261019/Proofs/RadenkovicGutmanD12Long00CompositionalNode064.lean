/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode062
import Proofs.RadenkovicGutmanD12Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,12]],[[0,0],[0,0]],[[108,180],[180,2]],[[0,0],[0]],[[3006,618],[618]],[[0,0],[0]],[[15882,696],[696]],[[0,0],[0]],[[37250,308],[308]],[[0,0],[0]],[[47932,52],[52]],[[0,0],[0]],[[36792,2],[2]],[[0]],[[17356]],[[0]],[[4994]],[[0]],[[832]],[[0]],[[70]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
