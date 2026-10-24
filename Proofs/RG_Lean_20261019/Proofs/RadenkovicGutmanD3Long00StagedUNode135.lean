/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode128
import Proofs.RadenkovicGutmanD3Long00StagedUNode134
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e135 : NestedArithmetic.Expr 3 := .times e128 e134
noncomputable def p135 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step135 : p135=NestedArithmetic.mul p128 p134 := by decide +kernel
#print axioms step135
theorem h135 : NestedArithmetic.compile e135=p135 := StagedExprCompile.compile_times e135 e128 e134 p128 p134 p135 rfl h128 h134 step135
#print axioms h135
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
