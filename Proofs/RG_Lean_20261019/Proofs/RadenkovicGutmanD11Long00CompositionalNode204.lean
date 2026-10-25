/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode194
import Proofs.RadenkovicGutmanD11Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[22],[0]],[[0,0],[0]],[[352,0],[0]],[[0,0],[0]],[[2354,0],[0]],[[0,0],[0]],[[8536,0],[0]],[[0,0],[0]],[[18216,0],[0]],[[0,0],[0]],[[23232,22],[22]],[[0,0],[0]],[[17138,154],[154]],[[0,0],[0]],[[6600,352],[352]],[[0,0],[0]],[[990,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
