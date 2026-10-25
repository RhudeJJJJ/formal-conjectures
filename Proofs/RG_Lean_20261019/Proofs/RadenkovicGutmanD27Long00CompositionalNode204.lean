/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode194
import Proofs.RadenkovicGutmanD27Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[54],[0]],[[0,0],[0]],[[864,0],[0]],[[0,0],[0]],[[5778,0],[0]],[[0,0],[0]],[[20952,0],[0]],[[0,0],[0]],[[44712,0],[0]],[[0,0],[0]],[[57024,54],[54]],[[0,0],[0]],[[42066,378],[378]],[[0,0],[0]],[[16200,864],[864]],[[0,0],[0]],[[2430,702],[702]],[[0,0],[0]],[[0,162],[162]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
