/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode045
import Proofs.RadenkovicGutmanD13Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,13]],[[0,0],[0,0]],[[-117,195],[195,2]],[[0,0],[0]],[[1425,668],[668]],[[0,0],[0]],[[12005,750],[750]],[[0,0],[0]],[[34160,330],[330]],[[0,0],[0]],[[50220,55],[55]],[[0,0],[0]],[[42852,2],[2]],[[0]],[[22007]],[[0]],[[6748]],[[0]],[[1163]],[[0]],[[95]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
