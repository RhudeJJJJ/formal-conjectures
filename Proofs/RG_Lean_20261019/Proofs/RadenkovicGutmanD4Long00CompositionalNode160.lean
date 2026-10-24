/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode154
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e009 e154
noncomputable def p160 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step160 : p160=NestedArithmetic.mul p009 p154 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e009 e154 p009 p154 p160 rfl h009 h154 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
