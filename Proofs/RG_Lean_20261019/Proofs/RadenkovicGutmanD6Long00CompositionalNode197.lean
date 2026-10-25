/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode193
import Proofs.RadenkovicGutmanD6Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[60,0],[0,0]],[[0,0],[0,0]],[[638,0],[0,0]],[[0,0],[0,0]],[[3458,0],[0,0]],[[0,0],[0,0]],[[10842,0],[0,0]],[[0,0],[0,0]],[[20592,2],[2,0]],[[0,0],[0,0]],[[23732,34],[34,0]],[[0,0],[0,0]],[[15946,176],[176,0]],[[0,0],[0,0]],[[5544,372],[372,0]],[[0,0],[0,0]],[[648,318],[318,0]],[[0,0],[0,0]],[[-54,90],[90,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
