/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode046
import Proofs.RadenkovicGutmanD3Long00StagedUNode055
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e046 e055
noncomputable def p062 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,18],[18]],[[0,0],[0]],[[270,78],[78]],[[0,0],[0]],[[1800,96],[96]],[[0,0],[0]],[[4674,42],[42]],[[0,0],[0]],[[6336,6],[6]],[[0]],[[4968]],[[0]],[[2328]],[[0]],[[642]],[[0]],[[96]],[[0]],[[6]]]
theorem step062 : p062=NestedArithmetic.mul p046 p055 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e046 e055 p046 p055 p062 rfl h046 h055 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
