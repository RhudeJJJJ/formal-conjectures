/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode065
import Proofs.RadenkovicGutmanD23Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-103,0],[0,0]],[[0,0],[0,0]],[[-1371,0],[0,0]],[[0,0],[0,0]],[[-8690,0],[0,0]],[[0,0],[0,0]],[[-31183,0],[0,0]],[[0,0],[0,0]],[[-67504,-2],[-2,0]],[[0,0],[0,0]],[[-89248,-85],[-85,0]],[[0,0],[0,0]],[[-70118,-550],[-550,0]],[[0,0],[0,0]],[[-30149,-1290],[-1290,0]],[[0,0],[0,0]],[[-5745,-1168],[-1168,0]],[[0,0],[0,0]],[[-207,-345],[-345,-2]],[[0],[0,0]],[[0],[0,-23]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
