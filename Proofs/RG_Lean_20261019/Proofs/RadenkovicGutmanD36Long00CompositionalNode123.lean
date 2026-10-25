/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode121
import Proofs.RadenkovicGutmanD36Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e123 : NestedArithmetic.Expr 3 := .times e121 e122
noncomputable def p123 : NestedHorner.Poly 3 := [[[1]]]
theorem step123 : p123=NestedArithmetic.mul p121 p122 := by decide +kernel
#print axioms step123
theorem h123 : NestedArithmetic.compile e123=p123 := StagedExprCompile.compile_times e123 e121 e122 p121 p122 p123 rfl h121 h122 step123
#print axioms h123
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
