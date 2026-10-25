/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode203
import Proofs.RadenkovicGutmanD15Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[79,0],[0,0]],[[0,0],[0,0]],[[979,0],[0,0]],[[0,0],[0,0]],[[6002,0],[0,0]],[[0,0],[0,0]],[[21127,0],[0,0]],[[0,0],[0,0]],[[45168,2],[2,0]],[[0,0],[0,0]],[[59200,61],[61,0]],[[0,0],[0,0]],[[46214,374],[374,0]],[[0,0],[0,0]],[[19773,858],[858,0]],[[0,0],[0,0]],[[3753,768],[768,0]],[[0,0],[0,0]],[[135,225],[225,2]],[[0],[0,0]],[[0],[0,15]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
