/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode139
import Proofs.RadenkovicGutmanD2Long00CompositionalNode134
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e140 : NestedArithmetic.Expr 3 := .times e139 e134
noncomputable def p140 : NestedHorner.Poly 3 := [[[1]],[[0]],[[6]],[[0]],[[11]],[[0]],[[6]]]
theorem step140 : p140=NestedArithmetic.mul p139 p134 := by decide +kernel
#print axioms step140
theorem h140 : NestedArithmetic.compile e140=p140 := StagedExprCompile.compile_times e140 e139 e134 p139 p134 p140 rfl h139 h134 step140
#print axioms h140
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
