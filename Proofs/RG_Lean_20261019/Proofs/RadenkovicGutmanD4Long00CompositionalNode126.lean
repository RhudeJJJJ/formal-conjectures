/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode125
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e126 : NestedArithmetic.Expr 3 := .times e125 e121
noncomputable def p126 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]]]
theorem step126 : p126=NestedArithmetic.mul p125 p121 := by decide +kernel
#print axioms step126
theorem h126 : NestedArithmetic.compile e126=p126 := StagedExprCompile.compile_times e126 e125 e121 p125 p121 p126 rfl h125 h121 step126
#print axioms h126
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
