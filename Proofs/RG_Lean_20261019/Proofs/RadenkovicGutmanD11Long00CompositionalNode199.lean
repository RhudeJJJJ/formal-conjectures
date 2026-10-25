/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode131
import Proofs.RadenkovicGutmanD11Long00CompositionalNode155
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e199 : NestedArithmetic.Expr 3 := .times e131 e155
noncomputable def p199 : NestedHorner.Poly 3 := [[[4]],[[0]],[[56]],[[0]],[[324]],[[0]],[[1000]],[[0]],[[1776]],[[0]],[[1832]],[[0]],[[1060]],[[0]],[[312]],[[0]],[[36]]]
theorem step199 : p199=NestedArithmetic.mul p131 p155 := by decide +kernel
#print axioms step199
theorem h199 : NestedArithmetic.compile e199=p199 := StagedExprCompile.compile_times e199 e131 e155 p131 p155 p199 rfl h131 h155 step199
#print axioms h199
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
