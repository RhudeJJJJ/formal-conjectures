/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode203
import Proofs.RadenkovicGutmanD17Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[85,0],[0,0]],[[0,0],[0,0]],[[1077,0],[0,0]],[[0,0],[0,0]],[[6674,0],[0,0]],[[0,0],[0,0]],[[23641,0],[0,0]],[[0,0],[0,0]],[[50752,2],[2,0]],[[0,0],[0,0]],[[66712,67],[67,0]],[[0,0],[0,0]],[[52190,418],[418,0]],[[0,0],[0,0]],[[22367,966],[966,0]],[[0,0],[0,0]],[[4251,868],[868,0]],[[0,0],[0,0]],[[153,255],[255,2]],[[0],[0,0]],[[0],[0,17]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
