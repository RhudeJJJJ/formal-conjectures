/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode045
import Proofs.RadenkovicGutmanD24Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,24]],[[0,0],[0,0]],[[-216,360],[360,2]],[[0,0],[0]],[[2646,1218],[1218]],[[0,0],[0]],[[22158,1344],[1344]],[[0,0],[0]],[[62782,572],[572]],[[0,0],[0]],[[91844,88],[88]],[[0,0],[0]],[[77832,2],[2]],[[0]],[[39552]],[[0]],[[11918]],[[0]],[[1988]],[[0]],[[150]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
