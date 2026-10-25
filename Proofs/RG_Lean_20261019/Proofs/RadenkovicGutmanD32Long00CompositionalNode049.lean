/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode045
import Proofs.RadenkovicGutmanD32Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,32]],[[0,0],[0,0]],[[-288,480],[480,2]],[[0,0],[0]],[[3534,1618],[1618]],[[0,0],[0]],[[29542,1776],[1776]],[[0,0],[0]],[[83598,748],[748]],[[0,0],[0]],[[122116,112],[112]],[[0,0],[0]],[[103272,2],[2]],[[0]],[[52312]],[[0]],[[15678]],[[0]],[[2588]],[[0]],[[190]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
