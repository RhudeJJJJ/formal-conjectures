/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode203
import Proofs.RadenkovicGutmanD37Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[145,0],[0,0]],[[0,0],[0,0]],[[2057,0],[0,0]],[[0,0],[0,0]],[[13394,0],[0,0]],[[0,0],[0,0]],[[48781,0],[0,0]],[[0,0],[0,0]],[[106592,2],[2,0]],[[0,0],[0,0]],[[141832,127],[127,0]],[[0,0],[0,0]],[[111950,858],[858,0]],[[0,0],[0,0]],[[48307,2046],[2046,0]],[[0,0],[0,0]],[[9231,1868],[1868,0]],[[0,0],[0,0]],[[333,555],[555,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
