/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode009
import Proofs.RadenkovicGutmanD2Long00CompositionalNode153
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e009 e153
noncomputable def p159 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step159 : p159=NestedArithmetic.mul p009 p153 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e009 e153 p009 p153 p159 rfl h009 h153 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
