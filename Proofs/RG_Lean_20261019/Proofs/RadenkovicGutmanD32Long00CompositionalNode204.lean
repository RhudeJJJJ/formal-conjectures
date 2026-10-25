/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode194
import Proofs.RadenkovicGutmanD32Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[64],[0]],[[0,0],[0]],[[1024,0],[0]],[[0,0],[0]],[[6848,0],[0]],[[0,0],[0]],[[24832,0],[0]],[[0,0],[0]],[[52992,0],[0]],[[0,0],[0]],[[67584,64],[64]],[[0,0],[0]],[[49856,448],[448]],[[0,0],[0]],[[19200,1024],[1024]],[[0,0],[0]],[[2880,832],[832]],[[0,0],[0]],[[0,192],[192]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
