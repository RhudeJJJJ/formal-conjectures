/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e032 : NestedArithmetic.Expr 3 := .times e002 e031
noncomputable def p032 : NestedHorner.Poly 3 := [[[0],[0,3]],[[0,0],[0]],[[-27,27],[27]],[[0,0],[0]],[[9,72],[72]],[[0,0],[0]],[[501,66],[66]],[[0,0],[0]],[[1542,24],[24]],[[0,0],[0]],[[2268,3],[3]],[[0]],[[1908]],[[0]],[[957]],[[0]],[[282]],[[0]],[[45]],[[0]],[[3]]]
theorem step032 : p032=NestedArithmetic.mul p002 p031 := by decide +kernel
#print axioms step032
theorem h032 : NestedArithmetic.compile e032=p032 := StagedExprCompile.compile_times e032 e002 e031 p002 p031 p032 rfl h002 h031 step032
#print axioms h032
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
