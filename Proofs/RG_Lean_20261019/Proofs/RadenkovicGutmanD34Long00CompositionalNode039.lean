/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode009
import Proofs.RadenkovicGutmanD34Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e039 : NestedArithmetic.Expr 3 := .times e009 e014
noncomputable def p039 : NestedHorner.Poly 3 := [[[]],[[0]],[[36]],[[0]],[[312]],[[0]],[[1060]],[[0]],[[1832]],[[0]],[[1776]],[[0]],[[1000]],[[0]],[[324]],[[0]],[[56]],[[0]],[[4]]]
theorem step039 : p039=NestedArithmetic.mul p009 p014 := by decide +kernel
#print axioms step039
theorem h039 : NestedArithmetic.compile e039=p039 := StagedExprCompile.compile_times e039 e009 e014 p009 p014 p039 rfl h009 h014 step039
#print axioms h039
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
