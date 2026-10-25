/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode194
import Proofs.RadenkovicGutmanD22Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[44],[0]],[[0,0],[0]],[[704,0],[0]],[[0,0],[0]],[[4708,0],[0]],[[0,0],[0]],[[17072,0],[0]],[[0,0],[0]],[[36432,0],[0]],[[0,0],[0]],[[46464,44],[44]],[[0,0],[0]],[[34276,308],[308]],[[0,0],[0]],[[13200,704],[704]],[[0,0],[0]],[[1980,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
