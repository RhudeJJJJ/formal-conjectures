/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode062
import Proofs.RadenkovicGutmanD30Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,30]],[[0,0],[0,0]],[[270,450],[450,2]],[[0,0],[0]],[[7488,1518],[1518]],[[0,0],[0]],[[39228,1668],[1668]],[[0,0],[0]],[[91034,704],[704]],[[0,0],[0]],[[115540,106],[106]],[[0,0],[0]],[[87048,2],[2]],[[0]],[[39982]],[[0]],[[11042]],[[0]],[[1714]],[[0]],[[124]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
