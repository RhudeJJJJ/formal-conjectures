/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode194
import Proofs.RadenkovicGutmanD9Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[18],[0]],[[0,0],[0]],[[288,0],[0]],[[0,0],[0]],[[1926,0],[0]],[[0,0],[0]],[[6984,0],[0]],[[0,0],[0]],[[14904,0],[0]],[[0,0],[0]],[[19008,18],[18]],[[0,0],[0]],[[14022,126],[126]],[[0,0],[0]],[[5400,288],[288]],[[0,0],[0]],[[810,234],[234]],[[0,0],[0]],[[0,54],[54]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
