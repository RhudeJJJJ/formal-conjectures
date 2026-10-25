/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode010
import Proofs.RadenkovicGutmanD44Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e050 : NestedArithmetic.Expr 3 := .times e010 e014
noncomputable def p050 : NestedHorner.Poly 3 := [[[]],[[]],[[0]],[[0]],[[36]],[[0]],[[312]],[[0]],[[1060]],[[0]],[[1832]],[[0]],[[1776]],[[0]],[[1000]],[[0]],[[324]],[[0]],[[56]],[[0]],[[4]]]
theorem step050 : p050=NestedArithmetic.mul p010 p014 := by decide +kernel
#print axioms step050
theorem h050 : NestedArithmetic.compile e050=p050 := StagedExprCompile.compile_times e050 e010 e014 p010 p014 p050 rfl h010 h014 step050
#print axioms h050
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
