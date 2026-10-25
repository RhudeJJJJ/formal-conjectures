/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode193
import Proofs.RadenkovicGutmanD12Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[90,0],[0,0]],[[0,0],[0,0]],[[1088,0],[0,0]],[[0,0],[0,0]],[[6278,0],[0,0]],[[0,0],[0,0]],[[20412,0],[0,0]],[[0,0],[0,0]],[[39672,2],[2,0]],[[0,0],[0,0]],[[46436,52],[52,0]],[[0,0],[0,0]],[[31558,308],[308,0]],[[0,0],[0,0]],[[11082,696],[696,0]],[[0,0],[0,0]],[[1314,618],[618,0]],[[0,0],[0,0]],[[-108,180],[180,2]],[[0],[0,0]],[[0],[0,12]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
