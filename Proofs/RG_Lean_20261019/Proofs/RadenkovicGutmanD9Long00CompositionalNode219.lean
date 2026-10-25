/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode065
import Proofs.RadenkovicGutmanD9Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[9],[0]],[[0,0],[0]],[[144,0],[0]],[[0,0],[0]],[[963,0],[0]],[[0,0],[0]],[[3492,0],[0]],[[0,0],[0]],[[7452,0],[0]],[[0,0],[0]],[[9504,9],[9]],[[0,0],[0]],[[7011,63],[63]],[[0,0],[0]],[[2700,144],[144]],[[0,0],[0]],[[405,117],[117]],[[0,0],[0]],[[0,27],[27]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
