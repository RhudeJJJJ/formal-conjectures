/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode065
import Proofs.RadenkovicGutmanD17Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-85,0],[0,0]],[[0,0],[0,0]],[[-1077,0],[0,0]],[[0,0],[0,0]],[[-6674,0],[0,0]],[[0,0],[0,0]],[[-23641,0],[0,0]],[[0,0],[0,0]],[[-50752,-2],[-2,0]],[[0,0],[0,0]],[[-66712,-67],[-67,0]],[[0,0],[0,0]],[[-52190,-418],[-418,0]],[[0,0],[0,0]],[[-22367,-966],[-966,0]],[[0,0],[0,0]],[[-4251,-868],[-868,0]],[[0,0],[0,0]],[[-153,-255],[-255,-2]],[[0],[0,0]],[[0],[0,-17]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
