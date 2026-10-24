/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode065
import Proofs.RadenkovicGutmanD5Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-49,0],[0,0]],[[0,0],[0,0]],[[-489,0],[0,0]],[[0,0],[0,0]],[[-2642,0],[0,0]],[[0,0],[0,0]],[[-8557,0],[0,0]],[[0,0],[0,0]],[[-17248,-2],[-2,0]],[[0,0],[0,0]],[[-21640,-31],[-31,0]],[[0,0],[0,0]],[[-16334,-154],[-154,0]],[[0,0],[0,0]],[[-6803,-318],[-318,0]],[[0,0],[0,0]],[[-1263,-268],[-268,0]],[[0,0],[0,0]],[[-45,-75],[-75,-2]],[[0],[0,0]],[[0],[0,-5]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
