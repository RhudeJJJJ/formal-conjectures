/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode177
import Proofs.RadenkovicGutmanD24Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-748,0],[0,0]],[[0,0],[0,0]],[[-5368,0],[0,0]],[[0,0],[0,0]],[[-21164,0],[0,0]],[[0,0],[0,0]],[[-49984,0],[0,0]],[[0,0],[0,0]],[[-72336,-44],[-44,0]],[[0,0],[0,0]],[[-62920,-352],[-352,0]],[[0,0],[0,0]],[[-30668,-968],[-968,0]],[[0,0],[0,0]],[[-6996,-1056],[-1056,0]],[[0,0],[0,0]],[[-396,-396],[-396,0]],[[0],[0,0]],[[0],[0,-44]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
