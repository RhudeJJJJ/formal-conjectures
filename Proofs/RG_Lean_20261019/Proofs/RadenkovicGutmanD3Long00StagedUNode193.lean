/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode192
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e003
noncomputable def p193 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[12,0],[0]],[[0,0],[0]],[[180,0],[0]],[[0,0],[0]],[[1128,0],[0]],[[0,0],[0]],[[3828,0],[0]],[[0,0],[0]],[[7632,0],[0]],[[0,0],[0]],[[9084,6],[6]],[[0,0],[0]],[[6264,42],[42]],[[0,0],[0]],[[2268,96],[96]],[[0,0],[0]],[[324,78],[78]],[[0,0],[0]],[[0,18],[18]]]
theorem step193 : p193=NestedArithmetic.mul p192 p003 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e003 p192 p003 p193 rfl h192 h003 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
