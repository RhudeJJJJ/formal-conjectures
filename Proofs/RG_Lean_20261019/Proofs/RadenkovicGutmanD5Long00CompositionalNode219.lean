/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode065
import Proofs.RadenkovicGutmanD5Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[5],[0]],[[0,0],[0]],[[80,0],[0]],[[0,0],[0]],[[535,0],[0]],[[0,0],[0]],[[1940,0],[0]],[[0,0],[0]],[[4140,0],[0]],[[0,0],[0]],[[5280,5],[5]],[[0,0],[0]],[[3895,35],[35]],[[0,0],[0]],[[1500,80],[80]],[[0,0],[0]],[[225,65],[65]],[[0,0],[0]],[[0,15],[15]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
