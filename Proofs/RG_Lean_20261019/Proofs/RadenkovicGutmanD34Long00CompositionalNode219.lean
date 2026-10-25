/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode065
import Proofs.RadenkovicGutmanD34Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[34],[0]],[[0,0],[0]],[[544,0],[0]],[[0,0],[0]],[[3638,0],[0]],[[0,0],[0]],[[13192,0],[0]],[[0,0],[0]],[[28152,0],[0]],[[0,0],[0]],[[35904,34],[34]],[[0,0],[0]],[[26486,238],[238]],[[0,0],[0]],[[10200,544],[544]],[[0,0],[0]],[[1530,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
