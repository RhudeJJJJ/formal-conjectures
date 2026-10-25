/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode065
import Proofs.RadenkovicGutmanD18Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-88,0],[0,0]],[[0,0],[0,0]],[[-1126,0],[0,0]],[[0,0],[0,0]],[[-7010,0],[0,0]],[[0,0],[0,0]],[[-24898,0],[0,0]],[[0,0],[0,0]],[[-53544,-2],[-2,0]],[[0,0],[0,0]],[[-70468,-70],[-70,0]],[[0,0],[0,0]],[[-55178,-440],[-440,0]],[[0,0],[0,0]],[[-23664,-1020],[-1020,0]],[[0,0],[0,0]],[[-4500,-918],[-918,0]],[[0,0],[0,0]],[[-162,-270],[-270,-2]],[[0],[0,0]],[[0],[0,-18]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
