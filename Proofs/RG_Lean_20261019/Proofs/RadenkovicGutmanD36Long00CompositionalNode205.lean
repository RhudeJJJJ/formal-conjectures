/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode204
import Proofs.RadenkovicGutmanD36Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[72,0],[0]],[[0,0],[0]],[[1152,0],[0]],[[0,0],[0]],[[7704,0],[0]],[[0,0],[0]],[[27936,0],[0]],[[0,0],[0]],[[59616,0],[0]],[[0,0],[0]],[[76032,72],[72]],[[0,0],[0]],[[56088,504],[504]],[[0,0],[0]],[[21600,1152],[1152]],[[0,0],[0]],[[3240,936],[936]],[[0,0],[0]],[[0,216],[216]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
