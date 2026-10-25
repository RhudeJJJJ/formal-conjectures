/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode194
import Proofs.RadenkovicGutmanD24Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[48],[0]],[[0,0],[0]],[[768,0],[0]],[[0,0],[0]],[[5136,0],[0]],[[0,0],[0]],[[18624,0],[0]],[[0,0],[0]],[[39744,0],[0]],[[0,0],[0]],[[50688,48],[48]],[[0,0],[0]],[[37392,336],[336]],[[0,0],[0]],[[14400,768],[768]],[[0,0],[0]],[[2160,624],[624]],[[0,0],[0]],[[0,144],[144]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
