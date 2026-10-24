/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode159
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e003
noncomputable def p160 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step160 : p160=NestedArithmetic.mul p159 p003 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e003 p159 p003 p160 rfl h159 h003 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
