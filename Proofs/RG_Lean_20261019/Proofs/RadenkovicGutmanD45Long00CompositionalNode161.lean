/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode009
import Proofs.RadenkovicGutmanD45Long00CompositionalNode155
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e161 : NestedArithmetic.Expr 3 := .times e009 e155
noncomputable def p161 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step161 : p161=NestedArithmetic.mul p009 p155 := by decide +kernel
#print axioms step161
theorem h161 : NestedArithmetic.compile e161=p161 := StagedExprCompile.compile_times e161 e009 e155 p009 p155 p161 rfl h009 h155 step161
#print axioms h161
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
