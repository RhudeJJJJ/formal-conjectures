/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode193
import Proofs.RadenkovicGutmanD5Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[55,0],[0,0]],[[0,0],[0,0]],[[563,0],[0,0]],[[0,0],[0,0]],[[2988,0],[0,0]],[[0,0],[0,0]],[[9247,0],[0,0]],[[0,0],[0,0]],[[17412,2],[2,0]],[[0,0],[0,0]],[[19948,31],[31,0]],[[0,0],[0,0]],[[13344,154],[154,0]],[[0,0],[0,0]],[[4621,318],[318,0]],[[0,0],[0,0]],[[537,268],[268,0]],[[0,0],[0,0]],[[-45,75],[75,2]],[[0],[0,0]],[[0],[0,5]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
