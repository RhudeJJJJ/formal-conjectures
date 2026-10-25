/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode164
import Proofs.RadenkovicGutmanD23Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-622,0],[0,0]],[[0,0],[0,0]],[[-3836,0],[0,0]],[[0,0],[0,0]],[[-12750,0],[0,0]],[[0,0],[0,0]],[[-24712,0],[0,0]],[[0,0],[0,0]],[[-28200,-42],[-42,0]],[[0,0],[0,0]],[[-17924,-336],[-336,0]],[[0,0],[0,0]],[[-4894,-924],[-924,0]],[[0,0],[0,0]],[[498,-1008],[-1008,0]],[[0,0],[0,0]],[[450,-378],[-378,0]],[[0],[0,0]],[[0],[0,-42]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
