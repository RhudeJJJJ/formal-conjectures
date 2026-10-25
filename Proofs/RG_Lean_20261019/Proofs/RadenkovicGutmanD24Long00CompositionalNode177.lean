/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode174
import Proofs.RadenkovicGutmanD24Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-748,0],[0,0]],[[0,0],[0,0]],[[-5368,0],[0,0]],[[0,0],[0,0]],[[-21164,0],[0,0]],[[0,0],[0,0]],[[-49984,0],[0,0]],[[0,0],[0,0]],[[-72336,-44],[-44,0]],[[0,0],[0,0]],[[-62920,-352],[-352,0]],[[0,0],[0,0]],[[-30668,-968],[-968,0]],[[0,0],[0,0]],[[-6996,-1056],[-1056,0]],[[0,0],[0,0]],[[-396,-396],[-396,0]],[[0],[0,0]],[[0],[0,-44]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
