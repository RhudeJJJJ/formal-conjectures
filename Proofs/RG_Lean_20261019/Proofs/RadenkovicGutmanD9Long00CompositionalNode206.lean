/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode203
import Proofs.RadenkovicGutmanD9Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[61,0],[0,0]],[[0,0],[0,0]],[[685,0],[0,0]],[[0,0],[0,0]],[[3986,0],[0,0]],[[0,0],[0,0]],[[13585,0],[0,0]],[[0,0],[0,0]],[[28416,2],[2,0]],[[0,0],[0,0]],[[36664,43],[43,0]],[[0,0],[0,0]],[[28286,242],[242,0]],[[0,0],[0,0]],[[11991,534],[534,0]],[[0,0],[0,0]],[[2259,468],[468,0]],[[0,0],[0,0]],[[81,135],[135,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
