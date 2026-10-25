/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode161
import Proofs.RadenkovicGutmanD17Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e162 : NestedArithmetic.Expr 3 := .times e161 e003
noncomputable def p162 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step162 : p162=NestedArithmetic.mul p161 p003 := by decide +kernel
#print axioms step162
theorem h162 : NestedArithmetic.compile e162=p162 := StagedExprCompile.compile_times e162 e161 e003 p161 p003 p162 rfl h161 h003 step162
#print axioms h162
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
