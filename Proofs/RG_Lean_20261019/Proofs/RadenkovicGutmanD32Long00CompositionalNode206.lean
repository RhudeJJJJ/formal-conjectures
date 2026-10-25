/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode203
import Proofs.RadenkovicGutmanD32Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[130,0],[0,0]],[[0,0],[0,0]],[[1812,0],[0,0]],[[0,0],[0,0]],[[11714,0],[0,0]],[[0,0],[0,0]],[[42496,0],[0,0]],[[0,0],[0,0]],[[92632,2],[2,0]],[[0,0],[0,0]],[[123052,112],[112,0]],[[0,0],[0,0]],[[97010,748],[748,0]],[[0,0],[0,0]],[[41822,1776],[1776,0]],[[0,0],[0,0]],[[7986,1618],[1618,0]],[[0,0],[0,0]],[[288,480],[480,2]],[[0],[0,0]],[[0],[0,32]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
