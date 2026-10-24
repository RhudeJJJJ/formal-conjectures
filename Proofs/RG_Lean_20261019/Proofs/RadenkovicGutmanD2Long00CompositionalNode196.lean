/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode129
import Proofs.RadenkovicGutmanD2Long00CompositionalNode153
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e129 e153
noncomputable def p196 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step196 : p196=NestedArithmetic.mul p129 p153 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e129 e153 p129 p153 p196 rfl h129 h153 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
