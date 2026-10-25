/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode193
import Proofs.RadenkovicGutmanD22Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[140,0],[0,0]],[[0,0],[0,0]],[[1838,0],[0,0]],[[0,0],[0,0]],[[10978,0],[0,0]],[[0,0],[0,0]],[[36362,0],[0,0]],[[0,0],[0,0]],[[71472,2],[2,0]],[[0,0],[0,0]],[[84276,82],[82,0]],[[0,0],[0,0]],[[57578,528],[528,0]],[[0,0],[0,0]],[[20312,1236],[1236,0]],[[0,0],[0,0]],[[2424,1118],[1118,0]],[[0,0],[0,0]],[[-198,330],[330,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
