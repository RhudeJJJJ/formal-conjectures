/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode065
import Proofs.RadenkovicGutmanD27Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-115,0],[0,0]],[[0,0],[0,0]],[[-1567,0],[0,0]],[[0,0],[0,0]],[[-10034,0],[0,0]],[[0,0],[0,0]],[[-36211,0],[0,0]],[[0,0],[0,0]],[[-78672,-2],[-2,0]],[[0,0],[0,0]],[[-104272,-97],[-97,0]],[[0,0],[0,0]],[[-82070,-638],[-638,0]],[[0,0],[0,0]],[[-35337,-1506],[-1506,0]],[[0,0],[0,0]],[[-6741,-1368],[-1368,0]],[[0,0],[0,0]],[[-243,-405],[-405,-2]],[[0],[0,0]],[[0],[0,-27]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
