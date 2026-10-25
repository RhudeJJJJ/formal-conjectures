/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode193
import Proofs.RadenkovicGutmanD14Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[100,0],[0,0]],[[0,0],[0,0]],[[1238,0],[0,0]],[[0,0],[0,0]],[[7218,0],[0,0]],[[0,0],[0,0]],[[23602,0],[0,0]],[[0,0],[0,0]],[[46032,2],[2,0]],[[0,0],[0,0]],[[54004,58],[58,0]],[[0,0],[0,0]],[[36762,352],[352,0]],[[0,0],[0,0]],[[12928,804],[804,0]],[[0,0],[0,0]],[[1536,718],[718,0]],[[0,0],[0,0]],[[-126,210],[210,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
