/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode203
import Proofs.RadenkovicGutmanD22Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[100,0],[0,0]],[[0,0],[0,0]],[[1322,0],[0,0]],[[0,0],[0,0]],[[8354,0],[0,0]],[[0,0],[0,0]],[[29926,0],[0,0]],[[0,0],[0,0]],[[64712,2],[2,0]],[[0,0],[0,0]],[[85492,82],[82,0]],[[0,0],[0,0]],[[67130,528],[528,0]],[[0,0],[0,0]],[[28852,1236],[1236,0]],[[0,0],[0,0]],[[5496,1118],[1118,0]],[[0,0],[0,0]],[[198,330],[330,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
