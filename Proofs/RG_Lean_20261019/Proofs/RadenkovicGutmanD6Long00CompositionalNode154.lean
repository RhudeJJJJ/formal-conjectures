/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode153
import Proofs.RadenkovicGutmanD6Long00CompositionalNode136
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e154 : NestedArithmetic.Expr 3 := .times e153 e136
noncomputable def p154 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step154 : p154=NestedArithmetic.mul p153 p136 := by decide +kernel
#print axioms step154
theorem h154 : NestedArithmetic.compile e154=p154 := StagedExprCompile.compile_times e154 e153 e136 p153 p136 p154 rfl h153 h136 step154
#print axioms h154
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
