/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode203
import Proofs.RadenkovicGutmanD45Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[169,0],[0,0]],[[0,0],[0,0]],[[2449,0],[0,0]],[[0,0],[0,0]],[[16082,0],[0,0]],[[0,0],[0,0]],[[58837,0],[0,0]],[[0,0],[0,0]],[[128928,2],[2,0]],[[0,0],[0,0]],[[171880,151],[151,0]],[[0,0],[0,0]],[[135854,1034],[1034,0]],[[0,0],[0,0]],[[58683,2478],[2478,0]],[[0,0],[0,0]],[[11223,2268],[2268,0]],[[0,0],[0,0]],[[405,675],[675,2]],[[0],[0,0]],[[0],[0,45]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
