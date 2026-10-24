/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode121
import Proofs.RadenkovicGutmanD3Long00StagedUNode138
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e139 : NestedArithmetic.Expr 3 := .plus e121 e138
noncomputable def p139 : NestedHorner.Poly 3 := [[[1]],[[0]],[[2]]]
theorem step139 : p139=NestedHorner.add p121 p138 := by decide +kernel
#print axioms step139
theorem h139 : NestedArithmetic.compile e139=p139 := StagedExprCompile.compile_plus e139 e121 e138 p121 p138 p139 rfl h121 h138 step139
#print axioms h139
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
