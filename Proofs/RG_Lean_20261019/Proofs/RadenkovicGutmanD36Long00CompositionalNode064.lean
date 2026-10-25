/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode062
import Proofs.RadenkovicGutmanD36Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,36]],[[0,0],[0,0]],[[324,540],[540,2]],[[0,0],[0]],[[8982,1818],[1818]],[[0,0],[0]],[[47010,1992],[1992]],[[0,0],[0]],[[108962,836],[836]],[[0,0],[0]],[[138076,124],[124]],[[0,0],[0]],[[103800,2],[2]],[[0]],[[47524]],[[0]],[[13058]],[[0]],[[2008]],[[0]],[[142]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
