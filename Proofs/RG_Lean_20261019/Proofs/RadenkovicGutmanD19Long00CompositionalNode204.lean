/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode194
import Proofs.RadenkovicGutmanD19Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[38],[0]],[[0,0],[0]],[[608,0],[0]],[[0,0],[0]],[[4066,0],[0]],[[0,0],[0]],[[14744,0],[0]],[[0,0],[0]],[[31464,0],[0]],[[0,0],[0]],[[40128,38],[38]],[[0,0],[0]],[[29602,266],[266]],[[0,0],[0]],[[11400,608],[608]],[[0,0],[0]],[[1710,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
