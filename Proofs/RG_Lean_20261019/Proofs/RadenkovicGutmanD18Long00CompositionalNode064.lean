/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode062
import Proofs.RadenkovicGutmanD18Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,18]],[[0,0],[0,0]],[[162,270],[270,2]],[[0,0],[0]],[[4500,918],[918]],[[0,0],[0]],[[23664,1020],[1020]],[[0,0],[0]],[[55178,440],[440]],[[0,0],[0]],[[70468,70],[70]],[[0,0],[0]],[[53544,2],[2]],[[0]],[[24898]],[[0]],[[7010]],[[0]],[[1126]],[[0]],[[88]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
