/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode193
import Proofs.RadenkovicGutmanD42Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[240,0],[0,0]],[[0,0],[0,0]],[[3338,0],[0,0]],[[0,0],[0,0]],[[20378,0],[0,0]],[[0,0],[0,0]],[[68262,0],[0,0]],[[0,0],[0,0]],[[135072,2],[2,0]],[[0,0],[0,0]],[[159956,142],[142,0]],[[0,0],[0,0]],[[109618,968],[968,0]],[[0,0],[0,0]],[[38772,2316],[2316,0]],[[0,0],[0,0]],[[4644,2118],[2118,0]],[[0,0],[0,0]],[[-378,630],[630,2]],[[0],[0,0]],[[0],[0,42]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
