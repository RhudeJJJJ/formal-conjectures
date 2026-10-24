/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode002
import Proofs.RadenkovicGutmanD3Long00StagedUNode156
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e210 : NestedArithmetic.Expr 3 := .times e002 e156
noncomputable def p210 : NestedHorner.Poly 3 := [[[3],[0]],[[0,0],[0]],[[45,0],[0,0]],[[0,0],[0,0]],[[282,0],[0,0]],[[0,0],[0,0]],[[957,0],[0,0]],[[0,0],[0,0]],[[1908,0],[0,0]],[[0,0],[0,0]],[[2268,3],[3,0]],[[0,0],[0,0]],[[1542,24],[24,0]],[[0,0],[0,0]],[[501,66],[66,0]],[[0,0],[0,0]],[[9,72],[72,0]],[[0,0],[0,0]],[[-27,27],[27,0]],[[0],[0,0]],[[0],[0,3]]]
theorem step210 : p210=NestedArithmetic.mul p002 p156 := by decide +kernel
#print axioms step210
theorem h210 : NestedArithmetic.compile e210=p210 := StagedExprCompile.compile_times e210 e002 e156 p002 p156 p210 rfl h002 h156 step210
#print axioms h210
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
