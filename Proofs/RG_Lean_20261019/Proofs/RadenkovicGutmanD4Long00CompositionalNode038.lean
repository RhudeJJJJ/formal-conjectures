/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e009 e014
noncomputable def p038 : NestedHorner.Poly 3 := [[[]],[[0]],[[36]],[[0]],[[312]],[[0]],[[1060]],[[0]],[[1832]],[[0]],[[1776]],[[0]],[[1000]],[[0]],[[324]],[[0]],[[56]],[[0]],[[4]]]
theorem step038 : p038=NestedArithmetic.mul p009 p014 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e009 e014 p009 p014 p038 rfl h009 h014 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
