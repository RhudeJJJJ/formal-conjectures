/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode164
import Proofs.RadenkovicGutmanD8Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-172,0],[0,0]],[[0,0],[0,0]],[[-1016,0],[0,0]],[[0,0],[0,0]],[[-3180,0],[0,0]],[[0,0],[0,0]],[[-5632,0],[0,0]],[[0,0],[0,0]],[[-5520,-12],[-12,0]],[[0,0],[0,0]],[[-2504,-96],[-96,0]],[[0,0],[0,0]],[[116,-264],[-264,0]],[[0,0],[0,0]],[[588,-288],[-288,0]],[[0,0],[0,0]],[[180,-108],[-108,0]],[[0],[0,0]],[[0],[0,-12]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
