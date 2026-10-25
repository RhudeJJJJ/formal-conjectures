/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode030
import Proofs.RadenkovicGutmanD18Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[18],[0]],[[0,0],[0]],[[288,0],[0]],[[0,0],[0]],[[1926,0],[0]],[[0,0],[0]],[[6984,0],[0]],[[0,0],[0]],[[14904,0],[0]],[[0,0],[0]],[[19008,18],[18]],[[0,0],[0]],[[14022,126],[126]],[[0,0],[0]],[[5400,288],[288]],[[0,0],[0]],[[810,234],[234]],[[0,0],[0]],[[0,54],[54]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
