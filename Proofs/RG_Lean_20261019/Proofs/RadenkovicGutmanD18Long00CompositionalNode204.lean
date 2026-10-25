/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode194
import Proofs.RadenkovicGutmanD18Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[36],[0]],[[0,0],[0]],[[576,0],[0]],[[0,0],[0]],[[3852,0],[0]],[[0,0],[0]],[[13968,0],[0]],[[0,0],[0]],[[29808,0],[0]],[[0,0],[0]],[[38016,36],[36]],[[0,0],[0]],[[28044,252],[252]],[[0,0],[0]],[[10800,576],[576]],[[0,0],[0]],[[1620,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
