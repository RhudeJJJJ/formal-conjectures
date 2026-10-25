/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode030
import Proofs.RadenkovicGutmanD11Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[11],[0]],[[0,0],[0]],[[176,0],[0]],[[0,0],[0]],[[1177,0],[0]],[[0,0],[0]],[[4268,0],[0]],[[0,0],[0]],[[9108,0],[0]],[[0,0],[0]],[[11616,11],[11]],[[0,0],[0]],[[8569,77],[77]],[[0,0],[0]],[[3300,176],[176]],[[0,0],[0]],[[495,143],[143]],[[0,0],[0]],[[0,33],[33]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
