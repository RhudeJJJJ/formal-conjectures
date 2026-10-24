/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode191
import Proofs.RadenkovicGutmanD3Long00StagedUNode168
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e168
noncomputable def p192 : NestedHorner.Poly 3 := [[[12],[0]],[[0,0],[0]],[[180,0],[0]],[[0,0],[0]],[[1128,0],[0]],[[0,0],[0]],[[3828,0],[0]],[[0,0],[0]],[[7632,0],[0]],[[0,0],[0]],[[9084,6],[6]],[[0,0],[0]],[[6264,42],[42]],[[0,0],[0]],[[2268,96],[96]],[[0,0],[0]],[[324,78],[78]],[[0,0],[0]],[[0,18],[18]]]
theorem step192 : p192=NestedArithmetic.mul p191 p168 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e168 p191 p168 p192 rfl h191 h168 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
