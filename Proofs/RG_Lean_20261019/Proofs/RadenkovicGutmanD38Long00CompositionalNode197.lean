/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode193
import Proofs.RadenkovicGutmanD38Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[220,0],[0,0]],[[0,0],[0,0]],[[3038,0],[0,0]],[[0,0],[0,0]],[[18498,0],[0,0]],[[0,0],[0,0]],[[61882,0],[0,0]],[[0,0],[0,0]],[[122352,2],[2,0]],[[0,0],[0,0]],[[144820,130],[130,0]],[[0,0],[0,0]],[[99210,880],[880,0]],[[0,0],[0,0]],[[35080,2100],[2100,0]],[[0,0],[0,0]],[[4200,1918],[1918,0]],[[0,0],[0,0]],[[-342,570],[570,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
