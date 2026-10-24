/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode192
import Proofs.RadenkovicGutmanD4Long00CompositionalNode182
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e192 e182
noncomputable def p202 : NestedHorner.Poly 3 := [[[8],[0]],[[0,0],[0]],[[128,0],[0]],[[0,0],[0]],[[856,0],[0]],[[0,0],[0]],[[3104,0],[0]],[[0,0],[0]],[[6624,0],[0]],[[0,0],[0]],[[8448,8],[8]],[[0,0],[0]],[[6232,56],[56]],[[0,0],[0]],[[2400,128],[128]],[[0,0],[0]],[[360,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step202 : p202=NestedArithmetic.mul p192 p182 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e192 e182 p192 p182 p202 rfl h192 h182 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
