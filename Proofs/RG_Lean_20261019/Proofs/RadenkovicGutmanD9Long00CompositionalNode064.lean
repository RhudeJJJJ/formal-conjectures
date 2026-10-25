/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode062
import Proofs.RadenkovicGutmanD9Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,9]],[[0,0],[0,0]],[[81,135],[135,2]],[[0,0],[0]],[[2259,468],[468]],[[0,0],[0]],[[11991,534],[534]],[[0,0],[0]],[[28286,242],[242]],[[0,0],[0]],[[36664,43],[43]],[[0,0],[0]],[[28416,2],[2]],[[0]],[[13585]],[[0]],[[3986]],[[0]],[[685]],[[0]],[[61]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
