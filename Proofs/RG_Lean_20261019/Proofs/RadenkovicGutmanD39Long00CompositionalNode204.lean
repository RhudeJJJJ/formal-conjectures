/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode194
import Proofs.RadenkovicGutmanD39Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[78],[0]],[[0,0],[0]],[[1248,0],[0]],[[0,0],[0]],[[8346,0],[0]],[[0,0],[0]],[[30264,0],[0]],[[0,0],[0]],[[64584,0],[0]],[[0,0],[0]],[[82368,78],[78]],[[0,0],[0]],[[60762,546],[546]],[[0,0],[0]],[[23400,1248],[1248]],[[0,0],[0]],[[3510,1014],[1014]],[[0,0],[0]],[[0,234],[234]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
