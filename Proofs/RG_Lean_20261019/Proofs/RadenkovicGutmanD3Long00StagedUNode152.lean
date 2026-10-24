/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode151
import Proofs.RadenkovicGutmanD3Long00StagedUNode134
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e152 : NestedArithmetic.Expr 3 := .times e151 e134
noncomputable def p152 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step152 : p152=NestedArithmetic.mul p151 p134 := by decide +kernel
#print axioms step152
theorem h152 : NestedArithmetic.compile e152=p152 := StagedExprCompile.compile_times e152 e151 e134 p151 p134 p152 rfl h151 h134 step152
#print axioms h152
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
