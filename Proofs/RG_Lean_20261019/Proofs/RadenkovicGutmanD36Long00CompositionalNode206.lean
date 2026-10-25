/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode203
import Proofs.RadenkovicGutmanD36Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[142,0],[0,0]],[[0,0],[0,0]],[[2008,0],[0,0]],[[0,0],[0,0]],[[13058,0],[0,0]],[[0,0],[0,0]],[[47524,0],[0,0]],[[0,0],[0,0]],[[103800,2],[2,0]],[[0,0],[0,0]],[[138076,124],[124,0]],[[0,0],[0,0]],[[108962,836],[836,0]],[[0,0],[0,0]],[[47010,1992],[1992,0]],[[0,0],[0,0]],[[8982,1818],[1818,0]],[[0,0],[0,0]],[[324,540],[540,2]],[[0],[0,0]],[[0],[0,36]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
