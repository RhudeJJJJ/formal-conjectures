/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode065
import Proofs.RadenkovicGutmanD31Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-127,0],[0,0]],[[0,0],[0,0]],[[-1763,0],[0,0]],[[0,0],[0,0]],[[-11378,0],[0,0]],[[0,0],[0,0]],[[-41239,0],[0,0]],[[0,0],[0,0]],[[-89840,-2],[-2,0]],[[0,0],[0,0]],[[-119296,-109],[-109,0]],[[0,0],[0,0]],[[-94022,-726],[-726,0]],[[0,0],[0,0]],[[-40525,-1722],[-1722,0]],[[0,0],[0,0]],[[-7737,-1568],[-1568,0]],[[0,0],[0,0]],[[-279,-465],[-465,-2]],[[0],[0,0]],[[0],[0,-31]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
