/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode164
import Proofs.RadenkovicGutmanD24Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-652,0],[0,0]],[[0,0],[0,0]],[[-4024,0],[0,0]],[[0,0],[0,0]],[[-13388,0],[0,0]],[[0,0],[0,0]],[[-25984,0],[0,0]],[[0,0],[0,0]],[[-29712,-44],[-44,0]],[[0,0],[0,0]],[[-18952,-352],[-352,0]],[[0,0],[0,0]],[[-5228,-968],[-968,0]],[[0,0],[0,0]],[[492,-1056],[-1056,0]],[[0,0],[0,0]],[[468,-396],[-396,0]],[[0],[0,0]],[[0],[0,-44]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
