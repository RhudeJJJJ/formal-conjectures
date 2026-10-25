/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode065
import Proofs.RadenkovicGutmanD8Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[8],[0]],[[0,0],[0]],[[128,0],[0]],[[0,0],[0]],[[856,0],[0]],[[0,0],[0]],[[3104,0],[0]],[[0,0],[0]],[[6624,0],[0]],[[0,0],[0]],[[8448,8],[8]],[[0,0],[0]],[[6232,56],[56]],[[0,0],[0]],[[2400,128],[128]],[[0,0],[0]],[[360,104],[104]],[[0,0],[0]],[[0,24],[24]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
