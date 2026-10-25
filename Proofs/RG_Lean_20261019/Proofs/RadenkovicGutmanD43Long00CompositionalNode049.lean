/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode045
import Proofs.RadenkovicGutmanD43Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,43]],[[0,0],[0,0]],[[-387,645],[645,2]],[[0,0],[0]],[[4755,2168],[2168]],[[0,0],[0]],[[39695,2370],[2370]],[[0,0],[0]],[[112220,990],[990]],[[0,0],[0]],[[163740,145],[145]],[[0,0],[0]],[[138252,2],[2]],[[0]],[[69857]],[[0]],[[20848]],[[0]],[[3413]],[[0]],[[245]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
