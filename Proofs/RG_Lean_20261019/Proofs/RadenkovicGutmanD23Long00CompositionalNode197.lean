/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode193
import Proofs.RadenkovicGutmanD23Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[145,0],[0,0]],[[0,0],[0,0]],[[1913,0],[0,0]],[[0,0],[0,0]],[[11448,0],[0,0]],[[0,0],[0,0]],[[37957,0],[0,0]],[[0,0],[0,0]],[[74652,2],[2,0]],[[0,0],[0,0]],[[88060,85],[85,0]],[[0,0],[0,0]],[[60180,550],[550,0]],[[0,0],[0,0]],[[21235,1290],[1290,0]],[[0,0],[0,0]],[[2535,1168],[1168,0]],[[0,0],[0,0]],[[-207,345],[345,2]],[[0],[0,0]],[[0],[0,23]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
