/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e121 : NestedArithmetic.Expr 3 := .pow e000 0
noncomputable def p121 : NestedHorner.Poly 3 := [[[1]]]
theorem step121 : p121=NestedArithmetic.power p000 0 := by decide +kernel
#print axioms step121
theorem h121 : NestedArithmetic.compile e121=p121 := StagedExprCompile.compile_pow 0 e121 e000 p000 p121 rfl h000 step121
#print axioms h121
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
