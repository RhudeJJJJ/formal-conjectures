/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode062
import Proofs.RadenkovicGutmanD44Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,44]],[[0,0],[0,0]],[[396,660],[660,2]],[[0,0],[0]],[[10974,2218],[2218]],[[0,0],[0]],[[57386,2424],[2424]],[[0,0],[0]],[[132866,1012],[1012]],[[0,0],[0]],[[168124,148],[148]],[[0,0],[0]],[[126136,2],[2]],[[0]],[[57580]],[[0]],[[15746]],[[0]],[[2400]],[[0]],[[166]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
