/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode194
import Proofs.RadenkovicGutmanD6Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[12],[0]],[[0,0],[0]],[[192,0],[0]],[[0,0],[0]],[[1284,0],[0]],[[0,0],[0]],[[4656,0],[0]],[[0,0],[0]],[[9936,0],[0]],[[0,0],[0]],[[12672,12],[12]],[[0,0],[0]],[[9348,84],[84]],[[0,0],[0]],[[3600,192],[192]],[[0,0],[0]],[[540,156],[156]],[[0,0],[0]],[[0,36],[36]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
