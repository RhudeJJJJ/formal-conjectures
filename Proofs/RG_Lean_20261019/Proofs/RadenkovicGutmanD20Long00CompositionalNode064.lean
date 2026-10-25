/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode062
import Proofs.RadenkovicGutmanD20Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,20]],[[0,0],[0,0]],[[180,300],[300,2]],[[0,0],[0]],[[4998,1018],[1018]],[[0,0],[0]],[[26258,1128],[1128]],[[0,0],[0]],[[61154,484],[484]],[[0,0],[0]],[[77980,76],[76]],[[0,0],[0]],[[59128,2],[2]],[[0]],[[27412]],[[0]],[[7682]],[[0]],[[1224]],[[0]],[[94]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
