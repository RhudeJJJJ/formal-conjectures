/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode119
import Proofs.RadenkovicGutmanD24Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-652,0],[0,0]],[[0,0],[0,0]],[[-4024,0],[0,0]],[[0,0],[0,0]],[[-13388,0],[0,0]],[[0,0],[0,0]],[[-25984,0],[0,0]],[[0,0],[0,0]],[[-29712,-44],[-44,0]],[[0,0],[0,0]],[[-18952,-352],[-352,0]],[[0,0],[0,0]],[[-5228,-968],[-968,0]],[[0,0],[0,0]],[[492,-1056],[-1056,0]],[[0,0],[0,0]],[[468,-396],[-396,0]],[[0],[0,0]],[[0],[0,-44]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
