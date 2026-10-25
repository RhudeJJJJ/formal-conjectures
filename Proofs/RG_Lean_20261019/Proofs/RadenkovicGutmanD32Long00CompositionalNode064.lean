/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode062
import Proofs.RadenkovicGutmanD32Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,32]],[[0,0],[0,0]],[[288,480],[480,2]],[[0,0],[0]],[[7986,1618],[1618]],[[0,0],[0]],[[41822,1776],[1776]],[[0,0],[0]],[[97010,748],[748]],[[0,0],[0]],[[123052,112],[112]],[[0,0],[0]],[[92632,2],[2]],[[0]],[[42496]],[[0]],[[11714]],[[0]],[[1812]],[[0]],[[130]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
