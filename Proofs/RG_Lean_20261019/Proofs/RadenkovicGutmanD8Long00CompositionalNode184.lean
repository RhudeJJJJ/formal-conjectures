/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode030
import Proofs.RadenkovicGutmanD8Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[8],[0]],[[0,0],[0]],[[128,0],[0]],[[0,0],[0]],[[856,0],[0]],[[0,0],[0]],[[3104,0],[0]],[[0,0],[0]],[[6624,0],[0]],[[0,0],[0]],[[8448,8],[8]],[[0,0],[0]],[[6232,56],[56]],[[0,0],[0]],[[2400,128],[128]],[[0,0],[0]],[[360,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
