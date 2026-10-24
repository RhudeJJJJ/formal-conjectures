/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode138
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e188 : NestedArithmetic.Expr 3 := .times e138 e121
noncomputable def p188 : NestedHorner.Poly 3 := [[[2]]]
theorem step188 : p188=NestedArithmetic.mul p138 p121 := by decide +kernel
#print axioms step188
theorem h188 : NestedArithmetic.compile e188=p188 := StagedExprCompile.compile_times e188 e138 e121 p138 p121 p188 rfl h138 h121 step188
#print axioms h188
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
