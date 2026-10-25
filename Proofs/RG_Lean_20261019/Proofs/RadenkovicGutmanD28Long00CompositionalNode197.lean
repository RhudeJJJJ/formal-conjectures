/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode193
import Proofs.RadenkovicGutmanD28Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[170,0],[0,0]],[[0,0],[0,0]],[[2288,0],[0,0]],[[0,0],[0,0]],[[13798,0],[0,0]],[[0,0],[0,0]],[[45932,0],[0,0]],[[0,0],[0,0]],[[90552,2],[2,0]],[[0,0],[0,0]],[[106980,100],[100,0]],[[0,0],[0,0]],[[73190,660],[660,0]],[[0,0],[0,0]],[[25850,1560],[1560,0]],[[0,0],[0,0]],[[3090,1418],[1418,0]],[[0,0],[0,0]],[[-252,420],[420,2]],[[0],[0,0]],[[0],[0,28]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
