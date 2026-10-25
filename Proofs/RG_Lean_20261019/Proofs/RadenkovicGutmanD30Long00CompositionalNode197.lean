/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode193
import Proofs.RadenkovicGutmanD30Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[180,0],[0,0]],[[0,0],[0,0]],[[2438,0],[0,0]],[[0,0],[0,0]],[[14738,0],[0,0]],[[0,0],[0,0]],[[49122,0],[0,0]],[[0,0],[0,0]],[[96912,2],[2,0]],[[0,0],[0,0]],[[114548,106],[106,0]],[[0,0],[0,0]],[[78394,704],[704,0]],[[0,0],[0,0]],[[27696,1668],[1668,0]],[[0,0],[0,0]],[[3312,1518],[1518,0]],[[0,0],[0,0]],[[-270,450],[450,2]],[[0],[0,0]],[[0],[0,30]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
