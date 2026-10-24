/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode135
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e136 : NestedArithmetic.Expr 3 := .times e135 e120
noncomputable def p136 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step136 : p136=NestedArithmetic.mul p135 p120 := by decide +kernel
#print axioms step136
theorem h136 : NestedArithmetic.compile e136=p136 := StagedExprCompile.compile_times e136 e135 e120 p135 p120 p136 rfl h135 h120 step136
#print axioms h136
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
