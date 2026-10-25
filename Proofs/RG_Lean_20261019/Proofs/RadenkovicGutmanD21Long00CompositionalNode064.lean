/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode062
import Proofs.RadenkovicGutmanD21Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,21]],[[0,0],[0,0]],[[189,315],[315,2]],[[0,0],[0]],[[5247,1068],[1068]],[[0,0],[0]],[[27555,1182],[1182]],[[0,0],[0]],[[64142,506],[506]],[[0,0],[0]],[[81736,79],[79]],[[0,0],[0]],[[61920,2],[2]],[[0]],[[28669]],[[0]],[[8018]],[[0]],[[1273]],[[0]],[[97]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
