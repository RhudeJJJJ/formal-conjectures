/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode065
import Proofs.RadenkovicGutmanD11Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-67,0],[0,0]],[[0,0],[0,0]],[[-783,0],[0,0]],[[0,0],[0,0]],[[-4658,0],[0,0]],[[0,0],[0,0]],[[-16099,0],[0,0]],[[0,0],[0,0]],[[-34000,-2],[-2,0]],[[0,0],[0,0]],[[-44176,-49],[-49,0]],[[0,0],[0,0]],[[-34262,-286],[-286,0]],[[0,0],[0,0]],[[-14585,-642],[-642,0]],[[0,0],[0,0]],[[-2757,-568],[-568,0]],[[0,0],[0,0]],[[-99,-165],[-165,-2]],[[0],[0,0]],[[0],[0,-11]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
