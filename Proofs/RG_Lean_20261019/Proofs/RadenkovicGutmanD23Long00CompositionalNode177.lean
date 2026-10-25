/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode174
import Proofs.RadenkovicGutmanD23Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-714,0],[0,0]],[[0,0],[0,0]],[[-5124,0],[0,0]],[[0,0],[0,0]],[[-20202,0],[0,0]],[[0,0],[0,0]],[[-47712,0],[0,0]],[[0,0],[0,0]],[[-69048,-42],[-42,0]],[[0,0],[0,0]],[[-60060,-336],[-336,0]],[[0,0],[0,0]],[[-29274,-924],[-924,0]],[[0,0],[0,0]],[[-6678,-1008],[-1008,0]],[[0,0],[0,0]],[[-378,-378],[-378,0]],[[0],[0,0]],[[0],[0,-42]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
