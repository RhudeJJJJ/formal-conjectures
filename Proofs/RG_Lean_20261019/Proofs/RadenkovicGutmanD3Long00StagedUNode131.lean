/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode121
import Proofs.RadenkovicGutmanD3Long00StagedUNode130
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e131 : NestedArithmetic.Expr 3 := .plus e121 e130
noncomputable def p131 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]]]
theorem step131 : p131=NestedHorner.add p121 p130 := by decide +kernel
#print axioms step131
theorem h131 : NestedArithmetic.compile e131=p131 := StagedExprCompile.compile_plus e131 e121 e130 p121 p130 p131 rfl h121 h130 step131
#print axioms h131
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
