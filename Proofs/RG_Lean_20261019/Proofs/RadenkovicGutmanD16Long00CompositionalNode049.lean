/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode045
import Proofs.RadenkovicGutmanD16Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,16]],[[0,0],[0,0]],[[-144,240],[240,2]],[[0,0],[0]],[[1758,818],[818]],[[0,0],[0]],[[14774,912],[912]],[[0,0],[0]],[[41966,396],[396]],[[0,0],[0]],[[61572,64],[64]],[[0,0],[0]],[[52392,2],[2]],[[0]],[[26792]],[[0]],[[8158]],[[0]],[[1388]],[[0]],[[110]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
