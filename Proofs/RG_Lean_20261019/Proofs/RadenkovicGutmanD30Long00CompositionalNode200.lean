/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode199
import Proofs.RadenkovicGutmanD30Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e200 : NestedArithmetic.Expr 3 := .times e199 e003
noncomputable def p200 : NestedHorner.Poly 3 := [[[]],[[0]],[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step200 : p200=NestedArithmetic.mul p199 p003 := by decide +kernel
#print axioms step200
theorem h200 : NestedArithmetic.compile e200=p200 := StagedExprCompile.compile_times e200 e199 e003 p199 p003 p200 rfl h199 h003 step200
#print axioms h200
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
