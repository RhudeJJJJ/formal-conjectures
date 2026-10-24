/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode010
import Proofs.RadenkovicGutmanD4Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .times e010 e014
noncomputable def p049 : NestedHorner.Poly 3 := [[[]],[[]],[[0]],[[0]],[[36]],[[0]],[[312]],[[0]],[[1060]],[[0]],[[1832]],[[0]],[[1776]],[[0]],[[1000]],[[0]],[[324]],[[0]],[[56]],[[0]],[[4]]]
theorem step049 : p049=NestedArithmetic.mul p010 p014 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_times e049 e010 e014 p010 p014 p049 rfl h010 h014 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
