/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode194
import Proofs.RadenkovicGutmanD34Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[68],[0]],[[0,0],[0]],[[1088,0],[0]],[[0,0],[0]],[[7276,0],[0]],[[0,0],[0]],[[26384,0],[0]],[[0,0],[0]],[[56304,0],[0]],[[0,0],[0]],[[71808,68],[68]],[[0,0],[0]],[[52972,476],[476]],[[0,0],[0]],[[20400,1088],[1088]],[[0,0],[0]],[[3060,884],[884]],[[0,0],[0]],[[0,204],[204]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
