/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode203
import Proofs.RadenkovicGutmanD44Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[166,0],[0,0]],[[0,0],[0,0]],[[2400,0],[0,0]],[[0,0],[0,0]],[[15746,0],[0,0]],[[0,0],[0,0]],[[57580,0],[0,0]],[[0,0],[0,0]],[[126136,2],[2,0]],[[0,0],[0,0]],[[168124,148],[148,0]],[[0,0],[0,0]],[[132866,1012],[1012,0]],[[0,0],[0,0]],[[57386,2424],[2424,0]],[[0,0],[0,0]],[[10974,2218],[2218,0]],[[0,0],[0,0]],[[396,660],[660,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
