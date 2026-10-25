/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode194
import Proofs.RadenkovicGutmanD28Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[56],[0]],[[0,0],[0]],[[896,0],[0]],[[0,0],[0]],[[5992,0],[0]],[[0,0],[0]],[[21728,0],[0]],[[0,0],[0]],[[46368,0],[0]],[[0,0],[0]],[[59136,56],[56]],[[0,0],[0]],[[43624,392],[392]],[[0,0],[0]],[[16800,896],[896]],[[0,0],[0]],[[2520,728],[728]],[[0,0],[0]],[[0,168],[168]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
