/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode203
import Proofs.RadenkovicGutmanD20Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[94,0],[0,0]],[[0,0],[0,0]],[[1224,0],[0,0]],[[0,0],[0,0]],[[7682,0],[0,0]],[[0,0],[0,0]],[[27412,0],[0,0]],[[0,0],[0,0]],[[59128,2],[2,0]],[[0,0],[0,0]],[[77980,76],[76,0]],[[0,0],[0,0]],[[61154,484],[484,0]],[[0,0],[0,0]],[[26258,1128],[1128,0]],[[0,0],[0,0]],[[4998,1018],[1018,0]],[[0,0],[0,0]],[[180,300],[300,2]],[[0],[0,0]],[[0],[0,20]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
