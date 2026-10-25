/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode030
import Proofs.RadenkovicGutmanD24Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[24],[0]],[[0,0],[0]],[[384,0],[0]],[[0,0],[0]],[[2568,0],[0]],[[0,0],[0]],[[9312,0],[0]],[[0,0],[0]],[[19872,0],[0]],[[0,0],[0]],[[25344,24],[24]],[[0,0],[0]],[[18696,168],[168]],[[0,0],[0]],[[7200,384],[384]],[[0,0],[0]],[[1080,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
