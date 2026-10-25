/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode194
import Proofs.RadenkovicGutmanD14Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[28],[0]],[[0,0],[0]],[[448,0],[0]],[[0,0],[0]],[[2996,0],[0]],[[0,0],[0]],[[10864,0],[0]],[[0,0],[0]],[[23184,0],[0]],[[0,0],[0]],[[29568,28],[28]],[[0,0],[0]],[[21812,196],[196]],[[0,0],[0]],[[8400,448],[448]],[[0,0],[0]],[[1260,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
