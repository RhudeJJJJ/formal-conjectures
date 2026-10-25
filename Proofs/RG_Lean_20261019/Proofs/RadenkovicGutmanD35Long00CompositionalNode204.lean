/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode194
import Proofs.RadenkovicGutmanD35Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[70],[0]],[[0,0],[0]],[[1120,0],[0]],[[0,0],[0]],[[7490,0],[0]],[[0,0],[0]],[[27160,0],[0]],[[0,0],[0]],[[57960,0],[0]],[[0,0],[0]],[[73920,70],[70]],[[0,0],[0]],[[54530,490],[490]],[[0,0],[0]],[[21000,1120],[1120]],[[0,0],[0]],[[3150,910],[910]],[[0,0],[0]],[[0,210],[210]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
