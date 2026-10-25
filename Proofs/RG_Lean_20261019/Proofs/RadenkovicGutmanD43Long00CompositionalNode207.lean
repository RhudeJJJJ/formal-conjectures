/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode065
import Proofs.RadenkovicGutmanD43Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-163,0],[0,0]],[[0,0],[0,0]],[[-2351,0],[0,0]],[[0,0],[0,0]],[[-15410,0],[0,0]],[[0,0],[0,0]],[[-56323,0],[0,0]],[[0,0],[0,0]],[[-123344,-2],[-2,0]],[[0,0],[0,0]],[[-164368,-145],[-145,0]],[[0,0],[0,0]],[[-129878,-990],[-990,0]],[[0,0],[0,0]],[[-56089,-2370],[-2370,0]],[[0,0],[0,0]],[[-10725,-2168],[-2168,0]],[[0,0],[0,0]],[[-387,-645],[-645,-2]],[[0],[0,0]],[[0],[0,-43]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
