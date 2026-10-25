/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode065
import Proofs.RadenkovicGutmanD24Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-106,0],[0,0]],[[0,0],[0,0]],[[-1420,0],[0,0]],[[0,0],[0,0]],[[-9026,0],[0,0]],[[0,0],[0,0]],[[-32440,0],[0,0]],[[0,0],[0,0]],[[-70296,-2],[-2,0]],[[0,0],[0,0]],[[-93004,-88],[-88,0]],[[0,0],[0,0]],[[-73106,-572],[-572,0]],[[0,0],[0,0]],[[-31446,-1344],[-1344,0]],[[0,0],[0,0]],[[-5994,-1218],[-1218,0]],[[0,0],[0,0]],[[-216,-360],[-360,-2]],[[0],[0,0]],[[0],[0,-24]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
