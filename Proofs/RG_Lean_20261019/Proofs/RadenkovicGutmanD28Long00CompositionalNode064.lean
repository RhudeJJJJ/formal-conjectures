/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode062
import Proofs.RadenkovicGutmanD28Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,28]],[[0,0],[0,0]],[[252,420],[420,2]],[[0,0],[0]],[[6990,1418],[1418]],[[0,0],[0]],[[36634,1560],[1560]],[[0,0],[0]],[[85058,660],[660]],[[0,0],[0]],[[108028,100],[100]],[[0,0],[0]],[[81464,2],[2]],[[0]],[[37468]],[[0]],[[10370]],[[0]],[[1616]],[[0]],[[118]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
