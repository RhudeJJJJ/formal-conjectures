/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode120
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e122 : NestedArithmetic.Expr 3 := .times e120 e121
noncomputable def p122 : NestedHorner.Poly 3 := [[[1]]]
theorem step122 : p122=NestedArithmetic.mul p120 p121 := by decide +kernel
#print axioms step122
theorem h122 : NestedArithmetic.compile e122=p122 := StagedExprCompile.compile_times e122 e120 e121 p120 p121 p122 rfl h120 h121 step122
#print axioms h122
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
