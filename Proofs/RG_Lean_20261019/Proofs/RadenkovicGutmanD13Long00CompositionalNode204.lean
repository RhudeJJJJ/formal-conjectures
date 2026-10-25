/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode194
import Proofs.RadenkovicGutmanD13Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[26],[0]],[[0,0],[0]],[[416,0],[0]],[[0,0],[0]],[[2782,0],[0]],[[0,0],[0]],[[10088,0],[0]],[[0,0],[0]],[[21528,0],[0]],[[0,0],[0]],[[27456,26],[26]],[[0,0],[0]],[[20254,182],[182]],[[0,0],[0]],[[7800,416],[416]],[[0,0],[0]],[[1170,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
