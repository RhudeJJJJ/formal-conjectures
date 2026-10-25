/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode194
import Proofs.RadenkovicGutmanD36Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[72],[0]],[[0,0],[0]],[[1152,0],[0]],[[0,0],[0]],[[7704,0],[0]],[[0,0],[0]],[[27936,0],[0]],[[0,0],[0]],[[59616,0],[0]],[[0,0],[0]],[[76032,72],[72]],[[0,0],[0]],[[56088,504],[504]],[[0,0],[0]],[[21600,1152],[1152]],[[0,0],[0]],[[3240,936],[936]],[[0,0],[0]],[[0,216],[216]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
