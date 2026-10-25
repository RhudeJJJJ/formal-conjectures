/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode193
import Proofs.RadenkovicGutmanD39Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[225,0],[0,0]],[[0,0],[0,0]],[[3113,0],[0,0]],[[0,0],[0,0]],[[18968,0],[0,0]],[[0,0],[0,0]],[[63477,0],[0,0]],[[0,0],[0,0]],[[125532,2],[2,0]],[[0,0],[0,0]],[[148604,133],[133,0]],[[0,0],[0,0]],[[101812,902],[902,0]],[[0,0],[0,0]],[[36003,2154],[2154,0]],[[0,0],[0,0]],[[4311,1968],[1968,0]],[[0,0],[0,0]],[[-351,585],[585,2]],[[0],[0,0]],[[0],[0,39]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
