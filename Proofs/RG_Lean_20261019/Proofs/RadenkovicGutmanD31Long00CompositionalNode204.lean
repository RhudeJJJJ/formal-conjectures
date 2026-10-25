/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode194
import Proofs.RadenkovicGutmanD31Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[62],[0]],[[0,0],[0]],[[992,0],[0]],[[0,0],[0]],[[6634,0],[0]],[[0,0],[0]],[[24056,0],[0]],[[0,0],[0]],[[51336,0],[0]],[[0,0],[0]],[[65472,62],[62]],[[0,0],[0]],[[48298,434],[434]],[[0,0],[0]],[[18600,992],[992]],[[0,0],[0]],[[2790,806],[806]],[[0,0],[0]],[[0,186],[186]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
