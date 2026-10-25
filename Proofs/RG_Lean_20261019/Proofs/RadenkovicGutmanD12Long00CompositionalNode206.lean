/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode203
import Proofs.RadenkovicGutmanD12Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[70,0],[0,0]],[[0,0],[0,0]],[[832,0],[0,0]],[[0,0],[0,0]],[[4994,0],[0,0]],[[0,0],[0,0]],[[17356,0],[0,0]],[[0,0],[0,0]],[[36792,2],[2,0]],[[0,0],[0,0]],[[47932,52],[52,0]],[[0,0],[0,0]],[[37250,308],[308,0]],[[0,0],[0,0]],[[15882,696],[696,0]],[[0,0],[0,0]],[[3006,618],[618,0]],[[0,0],[0,0]],[[108,180],[180,2]],[[0],[0,0]],[[0],[0,12]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
