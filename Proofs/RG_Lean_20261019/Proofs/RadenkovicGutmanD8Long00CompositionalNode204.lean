/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode194
import Proofs.RadenkovicGutmanD8Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[16],[0]],[[0,0],[0]],[[256,0],[0]],[[0,0],[0]],[[1712,0],[0]],[[0,0],[0]],[[6208,0],[0]],[[0,0],[0]],[[13248,0],[0]],[[0,0],[0]],[[16896,16],[16]],[[0,0],[0]],[[12464,112],[112]],[[0,0],[0]],[[4800,256],[256]],[[0,0],[0]],[[720,208],[208]],[[0,0],[0]],[[0,48],[48]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
