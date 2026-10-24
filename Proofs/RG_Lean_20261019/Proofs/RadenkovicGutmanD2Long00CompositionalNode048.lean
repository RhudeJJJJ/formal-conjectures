/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode010
import Proofs.RadenkovicGutmanD2Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e010 e014
noncomputable def p048 : NestedHorner.Poly 3 := [[[]],[[]],[[0]],[[0]],[[36]],[[0]],[[312]],[[0]],[[1060]],[[0]],[[1832]],[[0]],[[1776]],[[0]],[[1000]],[[0]],[[324]],[[0]],[[56]],[[0]],[[4]]]
theorem step048 : p048=NestedArithmetic.mul p010 p014 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e010 e014 p010 p014 p048 rfl h010 h014 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
