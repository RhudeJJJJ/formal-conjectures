/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode203
import Proofs.RadenkovicGutmanD42Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[160,0],[0,0]],[[0,0],[0,0]],[[2302,0],[0,0]],[[0,0],[0,0]],[[15074,0],[0,0]],[[0,0],[0,0]],[[55066,0],[0,0]],[[0,0],[0,0]],[[120552,2],[2,0]],[[0,0],[0,0]],[[160612,142],[142,0]],[[0,0],[0,0]],[[126890,968],[968,0]],[[0,0],[0,0]],[[54792,2316],[2316,0]],[[0,0],[0,0]],[[10476,2118],[2118,0]],[[0,0],[0,0]],[[378,630],[630,2]],[[0],[0,0]],[[0],[0,42]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
