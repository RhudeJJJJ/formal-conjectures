/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode045
import Proofs.RadenkovicGutmanD41Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,41]],[[0,0],[0,0]],[[-369,615],[615,2]],[[0,0],[0]],[[4533,2068],[2068]],[[0,0],[0]],[[37849,2262],[2262]],[[0,0],[0]],[[107016,946],[946]],[[0,0],[0]],[[156172,139],[139]],[[0,0],[0]],[[131892,2],[2]],[[0]],[[66667]],[[0]],[[19908]],[[0]],[[3263]],[[0]],[[235]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
