/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode062
import Proofs.RadenkovicGutmanD23Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,23]],[[0,0],[0,0]],[[207,345],[345,2]],[[0,0],[0]],[[5745,1168],[1168]],[[0,0],[0]],[[30149,1290],[1290]],[[0,0],[0]],[[70118,550],[550]],[[0,0],[0]],[[89248,85],[85]],[[0,0],[0]],[[67504,2],[2]],[[0]],[[31183]],[[0]],[[8690]],[[0]],[[1371]],[[0]],[[103]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
