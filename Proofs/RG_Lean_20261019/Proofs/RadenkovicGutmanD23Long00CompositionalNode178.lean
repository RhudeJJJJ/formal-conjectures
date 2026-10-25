/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode177
import Proofs.RadenkovicGutmanD23Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-714,0],[0,0]],[[0,0],[0,0]],[[-5124,0],[0,0]],[[0,0],[0,0]],[[-20202,0],[0,0]],[[0,0],[0,0]],[[-47712,0],[0,0]],[[0,0],[0,0]],[[-69048,-42],[-42,0]],[[0,0],[0,0]],[[-60060,-336],[-336,0]],[[0,0],[0,0]],[[-29274,-924],[-924,0]],[[0,0],[0,0]],[[-6678,-1008],[-1008,0]],[[0,0],[0,0]],[[-378,-378],[-378,0]],[[0],[0,0]],[[0],[0,-42]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
