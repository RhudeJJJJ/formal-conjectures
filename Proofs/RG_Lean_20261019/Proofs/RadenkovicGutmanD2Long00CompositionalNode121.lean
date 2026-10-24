/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode119
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e121 : NestedArithmetic.Expr 3 := .times e119 e120
noncomputable def p121 : NestedHorner.Poly 3 := [[[1]]]
theorem step121 : p121=NestedArithmetic.mul p119 p120 := by decide +kernel
#print axioms step121
theorem h121 : NestedArithmetic.compile e121=p121 := StagedExprCompile.compile_times e121 e119 e120 p119 p120 p121 rfl h119 h120 step121
#print axioms h121
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
