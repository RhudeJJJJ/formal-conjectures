/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode065
import Proofs.RadenkovicGutmanD24Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[24],[0]],[[0,0],[0]],[[384,0],[0]],[[0,0],[0]],[[2568,0],[0]],[[0,0],[0]],[[9312,0],[0]],[[0,0],[0]],[[19872,0],[0]],[[0,0],[0]],[[25344,24],[24]],[[0,0],[0]],[[18696,168],[168]],[[0,0],[0]],[[7200,384],[384]],[[0,0],[0]],[[1080,312],[312]],[[0,0],[0]],[[0,72],[72]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
