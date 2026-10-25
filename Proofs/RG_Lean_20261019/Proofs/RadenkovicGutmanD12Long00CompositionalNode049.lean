/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode045
import Proofs.RadenkovicGutmanD12Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,12]],[[0,0],[0,0]],[[-108,180],[180,2]],[[0,0],[0]],[[1314,618],[618]],[[0,0],[0]],[[11082,696],[696]],[[0,0],[0]],[[31558,308],[308]],[[0,0],[0]],[[46436,52],[52]],[[0,0],[0]],[[39672,2],[2]],[[0]],[[20412]],[[0]],[[6278]],[[0]],[[1088]],[[0]],[[90]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
