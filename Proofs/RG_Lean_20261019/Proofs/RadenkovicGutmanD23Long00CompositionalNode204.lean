/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode194
import Proofs.RadenkovicGutmanD23Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[46],[0]],[[0,0],[0]],[[736,0],[0]],[[0,0],[0]],[[4922,0],[0]],[[0,0],[0]],[[17848,0],[0]],[[0,0],[0]],[[38088,0],[0]],[[0,0],[0]],[[48576,46],[46]],[[0,0],[0]],[[35834,322],[322]],[[0,0],[0]],[[13800,736],[736]],[[0,0],[0]],[[2070,598],[598]],[[0,0],[0]],[[0,138],[138]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
