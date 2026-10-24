/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode187
import Proofs.RadenkovicGutmanD3Long00StagedUNode004
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e188 : NestedArithmetic.Expr 3 := .plus e187 e004
noncomputable def p188 : NestedHorner.Poly 3 := [[[2]],[[0]],[[3]]]
theorem step188 : p188=NestedHorner.add p187 p004 := by decide +kernel
#print axioms step188
theorem h188 : NestedArithmetic.compile e188=p188 := StagedExprCompile.compile_plus e188 e187 e004 p187 p004 p188 rfl h187 h004 step188
#print axioms h188
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
