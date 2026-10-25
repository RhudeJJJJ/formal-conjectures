/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode193
import Proofs.RadenkovicGutmanD27Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[165,0],[0,0]],[[0,0],[0,0]],[[2213,0],[0,0]],[[0,0],[0,0]],[[13328,0],[0,0]],[[0,0],[0,0]],[[44337,0],[0,0]],[[0,0],[0,0]],[[87372,2],[2,0]],[[0,0],[0,0]],[[103196,97],[97,0]],[[0,0],[0,0]],[[70588,638],[638,0]],[[0,0],[0,0]],[[24927,1506],[1506,0]],[[0,0],[0,0]],[[2979,1368],[1368,0]],[[0,0],[0,0]],[[-243,405],[405,2]],[[0],[0,0]],[[0],[0,27]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
