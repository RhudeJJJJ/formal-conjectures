/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode036
import Proofs.RadenkovicGutmanD3Long00StagedUNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e036 e056
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0]],[[0,9],[9]],[[0,0],[0]],[[135,39],[39]],[[0,0],[0]],[[900,48],[48]],[[0,0],[0]],[[2337,21],[21]],[[0,0],[0]],[[3168,3],[3]],[[0]],[[2484]],[[0]],[[1164]],[[0]],[[321]],[[0]],[[48]],[[0]],[[3]]]
theorem step072 : p072=NestedArithmetic.mul p036 p056 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e036 e056 p036 p056 p072 rfl h036 h056 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
