/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode130
import Proofs.RadenkovicGutmanD4Long00CompositionalNode154
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .times e130 e154
noncomputable def p197 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step197 : p197=NestedArithmetic.mul p130 p154 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_times e197 e130 e154 p130 p154 p197 rfl h130 h154 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
