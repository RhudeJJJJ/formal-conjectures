/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode193
import Proofs.RadenkovicGutmanD7Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[65,0],[0,0]],[[0,0],[0,0]],[[713,0],[0,0]],[[0,0],[0,0]],[[3928,0],[0,0]],[[0,0],[0,0]],[[12437,0],[0,0]],[[0,0],[0,0]],[[23772,2],[2,0]],[[0,0],[0,0]],[[27516,37],[37,0]],[[0,0],[0,0]],[[18548,198],[198,0]],[[0,0],[0,0]],[[6467,426],[426,0]],[[0,0],[0,0]],[[759,368],[368,0]],[[0,0],[0,0]],[[-63,105],[105,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
