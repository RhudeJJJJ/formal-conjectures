/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode193
import Proofs.RadenkovicGutmanD13Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[95,0],[0,0]],[[0,0],[0,0]],[[1163,0],[0,0]],[[0,0],[0,0]],[[6748,0],[0,0]],[[0,0],[0,0]],[[22007,0],[0,0]],[[0,0],[0,0]],[[42852,2],[2,0]],[[0,0],[0,0]],[[50220,55],[55,0]],[[0,0],[0,0]],[[34160,330],[330,0]],[[0,0],[0,0]],[[12005,750],[750,0]],[[0,0],[0,0]],[[1425,668],[668,0]],[[0,0],[0,0]],[[-117,195],[195,2]],[[0],[0,0]],[[0],[0,13]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
