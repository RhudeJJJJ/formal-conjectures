/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode193
import Proofs.RadenkovicGutmanD19Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[125,0],[0,0]],[[0,0],[0,0]],[[1613,0],[0,0]],[[0,0],[0,0]],[[9568,0],[0,0]],[[0,0],[0,0]],[[31577,0],[0,0]],[[0,0],[0,0]],[[61932,2],[2,0]],[[0,0],[0,0]],[[72924,73],[73,0]],[[0,0],[0,0]],[[49772,462],[462,0]],[[0,0],[0,0]],[[17543,1074],[1074,0]],[[0,0],[0,0]],[[2091,968],[968,0]],[[0,0],[0,0]],[[-171,285],[285,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
