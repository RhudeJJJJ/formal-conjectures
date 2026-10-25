/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode203
import Proofs.RadenkovicGutmanD10Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[64,0],[0,0]],[[0,0],[0,0]],[[734,0],[0,0]],[[0,0],[0,0]],[[4322,0],[0,0]],[[0,0],[0,0]],[[14842,0],[0,0]],[[0,0],[0,0]],[[31208,2],[2,0]],[[0,0],[0,0]],[[40420,46],[46,0]],[[0,0],[0,0]],[[31274,264],[264,0]],[[0,0],[0,0]],[[13288,588],[588,0]],[[0,0],[0,0]],[[2508,518],[518,0]],[[0,0],[0,0]],[[90,150],[150,2]],[[0],[0,0]],[[0],[0,10]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
