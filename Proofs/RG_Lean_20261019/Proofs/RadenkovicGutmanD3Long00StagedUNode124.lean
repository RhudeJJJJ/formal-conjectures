/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode121
import Proofs.RadenkovicGutmanD3Long00StagedUNode123
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e124 : NestedArithmetic.Expr 3 := .plus e121 e123
noncomputable def p124 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]]]
theorem step124 : p124=NestedHorner.add p121 p123 := by decide +kernel
#print axioms step124
theorem h124 : NestedArithmetic.compile e124=p124 := StagedExprCompile.compile_plus e124 e121 e123 p121 p123 p124 rfl h121 h123 step124
#print axioms h124
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
