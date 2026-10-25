/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode203
import Proofs.RadenkovicGutmanD18Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[88,0],[0,0]],[[0,0],[0,0]],[[1126,0],[0,0]],[[0,0],[0,0]],[[7010,0],[0,0]],[[0,0],[0,0]],[[24898,0],[0,0]],[[0,0],[0,0]],[[53544,2],[2,0]],[[0,0],[0,0]],[[70468,70],[70,0]],[[0,0],[0,0]],[[55178,440],[440,0]],[[0,0],[0,0]],[[23664,1020],[1020,0]],[[0,0],[0,0]],[[4500,918],[918,0]],[[0,0],[0,0]],[[162,270],[270,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
