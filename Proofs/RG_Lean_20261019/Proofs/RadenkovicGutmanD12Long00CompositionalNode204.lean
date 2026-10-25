/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode194
import Proofs.RadenkovicGutmanD12Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[24],[0]],[[0,0],[0]],[[384,0],[0]],[[0,0],[0]],[[2568,0],[0]],[[0,0],[0]],[[9312,0],[0]],[[0,0],[0]],[[19872,0],[0]],[[0,0],[0]],[[25344,24],[24]],[[0,0],[0]],[[18696,168],[168]],[[0,0],[0]],[[7200,384],[384]],[[0,0],[0]],[[1080,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
