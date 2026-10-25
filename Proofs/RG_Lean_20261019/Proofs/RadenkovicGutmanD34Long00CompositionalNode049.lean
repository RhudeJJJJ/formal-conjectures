/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode045
import Proofs.RadenkovicGutmanD34Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,34]],[[0,0],[0,0]],[[-306,510],[510,2]],[[0,0],[0]],[[3756,1718],[1718]],[[0,0],[0]],[[31388,1884],[1884]],[[0,0],[0]],[[88802,792],[792]],[[0,0],[0]],[[129684,118],[118]],[[0,0],[0]],[[109632,2],[2]],[[0]],[[55502]],[[0]],[[16618]],[[0]],[[2738]],[[0]],[[200]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
