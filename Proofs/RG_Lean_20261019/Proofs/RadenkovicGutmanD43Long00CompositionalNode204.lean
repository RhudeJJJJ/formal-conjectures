/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode194
import Proofs.RadenkovicGutmanD43Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[86],[0]],[[0,0],[0]],[[1376,0],[0]],[[0,0],[0]],[[9202,0],[0]],[[0,0],[0]],[[33368,0],[0]],[[0,0],[0]],[[71208,0],[0]],[[0,0],[0]],[[90816,86],[86]],[[0,0],[0]],[[66994,602],[602]],[[0,0],[0]],[[25800,1376],[1376]],[[0,0],[0]],[[3870,1118],[1118]],[[0,0],[0]],[[0,258],[258]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
