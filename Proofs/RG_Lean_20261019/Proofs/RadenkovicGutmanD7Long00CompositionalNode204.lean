/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode194
import Proofs.RadenkovicGutmanD7Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[14],[0]],[[0,0],[0]],[[224,0],[0]],[[0,0],[0]],[[1498,0],[0]],[[0,0],[0]],[[5432,0],[0]],[[0,0],[0]],[[11592,0],[0]],[[0,0],[0]],[[14784,14],[14]],[[0,0],[0]],[[10906,98],[98]],[[0,0],[0]],[[4200,224],[224]],[[0,0],[0]],[[630,182],[182]],[[0,0],[0]],[[0,42],[42]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
