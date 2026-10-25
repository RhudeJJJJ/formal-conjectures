/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode194
import Proofs.RadenkovicGutmanD38Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[76],[0]],[[0,0],[0]],[[1216,0],[0]],[[0,0],[0]],[[8132,0],[0]],[[0,0],[0]],[[29488,0],[0]],[[0,0],[0]],[[62928,0],[0]],[[0,0],[0]],[[80256,76],[76]],[[0,0],[0]],[[59204,532],[532]],[[0,0],[0]],[[22800,1216],[1216]],[[0,0],[0]],[[3420,988],[988]],[[0,0],[0]],[[0,228],[228]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
