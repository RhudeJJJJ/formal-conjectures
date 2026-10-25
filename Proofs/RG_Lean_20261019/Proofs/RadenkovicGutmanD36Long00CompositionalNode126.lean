/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode123
import Proofs.RadenkovicGutmanD36Long00CompositionalNode125
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e126 : NestedArithmetic.Expr 3 := .plus e123 e125
noncomputable def p126 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]]]
theorem step126 : p126=NestedHorner.add p123 p125 := by decide +kernel
#print axioms step126
theorem h126 : NestedArithmetic.compile e126=p126 := StagedExprCompile.compile_plus e126 e123 e125 p123 p125 p126 rfl h123 h125 step126
#print axioms h126
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
