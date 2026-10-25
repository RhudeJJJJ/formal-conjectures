/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode062
import Proofs.RadenkovicGutmanD42Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,42]],[[0,0],[0,0]],[[378,630],[630,2]],[[0,0],[0]],[[10476,2118],[2118]],[[0,0],[0]],[[54792,2316],[2316]],[[0,0],[0]],[[126890,968],[968]],[[0,0],[0]],[[160612,142],[142]],[[0,0],[0]],[[120552,2],[2]],[[0]],[[55066]],[[0]],[[15074]],[[0]],[[2302]],[[0]],[[160]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
