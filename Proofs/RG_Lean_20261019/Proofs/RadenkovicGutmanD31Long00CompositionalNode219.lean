/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode065
import Proofs.RadenkovicGutmanD31Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[31],[0]],[[0,0],[0]],[[496,0],[0]],[[0,0],[0]],[[3317,0],[0]],[[0,0],[0]],[[12028,0],[0]],[[0,0],[0]],[[25668,0],[0]],[[0,0],[0]],[[32736,31],[31]],[[0,0],[0]],[[24149,217],[217]],[[0,0],[0]],[[9300,496],[496]],[[0,0],[0]],[[1395,403],[403]],[[0,0],[0]],[[0,93],[93]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
