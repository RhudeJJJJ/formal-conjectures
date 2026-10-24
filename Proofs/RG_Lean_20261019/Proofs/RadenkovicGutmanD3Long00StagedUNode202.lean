/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode201
import Proofs.RadenkovicGutmanD3Long00StagedUNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e201 e003
noncomputable def p202 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[6,0],[0]],[[0,0],[0]],[[96,0],[0]],[[0,0],[0]],[[642,0],[0]],[[0,0],[0]],[[2328,0],[0]],[[0,0],[0]],[[4968,0],[0]],[[0,0],[0]],[[6336,6],[6]],[[0,0],[0]],[[4674,42],[42]],[[0,0],[0]],[[1800,96],[96]],[[0,0],[0]],[[270,78],[78]],[[0,0],[0]],[[0,18],[18]]]
theorem step202 : p202=NestedArithmetic.mul p201 p003 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e201 e003 p201 p003 p202 rfl h201 h003 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
