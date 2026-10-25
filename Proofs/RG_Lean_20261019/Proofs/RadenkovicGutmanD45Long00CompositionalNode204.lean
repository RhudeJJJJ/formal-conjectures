/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode194
import Proofs.RadenkovicGutmanD45Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[90],[0]],[[0,0],[0]],[[1440,0],[0]],[[0,0],[0]],[[9630,0],[0]],[[0,0],[0]],[[34920,0],[0]],[[0,0],[0]],[[74520,0],[0]],[[0,0],[0]],[[95040,90],[90]],[[0,0],[0]],[[70110,630],[630]],[[0,0],[0]],[[27000,1440],[1440]],[[0,0],[0]],[[4050,1170],[1170]],[[0,0],[0]],[[0,270],[270]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
