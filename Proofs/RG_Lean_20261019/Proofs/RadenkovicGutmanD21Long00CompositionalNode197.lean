/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode193
import Proofs.RadenkovicGutmanD21Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[135,0],[0,0]],[[0,0],[0,0]],[[1763,0],[0,0]],[[0,0],[0,0]],[[10508,0],[0,0]],[[0,0],[0,0]],[[34767,0],[0,0]],[[0,0],[0,0]],[[68292,2],[2,0]],[[0,0],[0,0]],[[80492,79],[79,0]],[[0,0],[0,0]],[[54976,506],[506,0]],[[0,0],[0,0]],[[19389,1182],[1182,0]],[[0,0],[0,0]],[[2313,1068],[1068,0]],[[0,0],[0,0]],[[-189,315],[315,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
