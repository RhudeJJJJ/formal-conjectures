/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode203
import Proofs.RadenkovicGutmanD43Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[163,0],[0,0]],[[0,0],[0,0]],[[2351,0],[0,0]],[[0,0],[0,0]],[[15410,0],[0,0]],[[0,0],[0,0]],[[56323,0],[0,0]],[[0,0],[0,0]],[[123344,2],[2,0]],[[0,0],[0,0]],[[164368,145],[145,0]],[[0,0],[0,0]],[[129878,990],[990,0]],[[0,0],[0,0]],[[56089,2370],[2370,0]],[[0,0],[0,0]],[[10725,2168],[2168,0]],[[0,0],[0,0]],[[387,645],[645,2]],[[0],[0,0]],[[0],[0,43]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
