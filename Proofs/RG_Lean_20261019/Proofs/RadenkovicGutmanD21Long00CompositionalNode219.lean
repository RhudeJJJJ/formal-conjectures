/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode065
import Proofs.RadenkovicGutmanD21Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[21],[0]],[[0,0],[0]],[[336,0],[0]],[[0,0],[0]],[[2247,0],[0]],[[0,0],[0]],[[8148,0],[0]],[[0,0],[0]],[[17388,0],[0]],[[0,0],[0]],[[22176,21],[21]],[[0,0],[0]],[[16359,147],[147]],[[0,0],[0]],[[6300,336],[336]],[[0,0],[0]],[[945,273],[273]],[[0,0],[0]],[[0,63],[63]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
