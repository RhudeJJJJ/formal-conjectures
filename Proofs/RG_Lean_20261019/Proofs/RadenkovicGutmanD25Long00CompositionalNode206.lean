/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode203
import Proofs.RadenkovicGutmanD25Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[109,0],[0,0]],[[0,0],[0,0]],[[1469,0],[0,0]],[[0,0],[0,0]],[[9362,0],[0,0]],[[0,0],[0,0]],[[33697,0],[0,0]],[[0,0],[0,0]],[[73088,2],[2,0]],[[0,0],[0,0]],[[96760,91],[91,0]],[[0,0],[0,0]],[[76094,594],[594,0]],[[0,0],[0,0]],[[32743,1398],[1398,0]],[[0,0],[0,0]],[[6243,1268],[1268,0]],[[0,0],[0,0]],[[225,375],[375,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
