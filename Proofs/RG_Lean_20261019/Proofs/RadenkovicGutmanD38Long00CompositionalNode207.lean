/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode065
import Proofs.RadenkovicGutmanD38Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-148,0],[0,0]],[[0,0],[0,0]],[[-2106,0],[0,0]],[[0,0],[0,0]],[[-13730,0],[0,0]],[[0,0],[0,0]],[[-50038,0],[0,0]],[[0,0],[0,0]],[[-109384,-2],[-2,0]],[[0,0],[0,0]],[[-145588,-130],[-130,0]],[[0,0],[0,0]],[[-114938,-880],[-880,0]],[[0,0],[0,0]],[[-49604,-2100],[-2100,0]],[[0,0],[0,0]],[[-9480,-1918],[-1918,0]],[[0,0],[0,0]],[[-342,-570],[-570,-2]],[[0],[0,0]],[[0],[0,-38]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
