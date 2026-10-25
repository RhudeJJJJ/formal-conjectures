/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode065
import Proofs.RadenkovicGutmanD7Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-55,0],[0,0]],[[0,0],[0,0]],[[-587,0],[0,0]],[[0,0],[0,0]],[[-3314,0],[0,0]],[[0,0],[0,0]],[[-11071,0],[0,0]],[[0,0],[0,0]],[[-22832,-2],[-2,0]],[[0,0],[0,0]],[[-29152,-37],[-37,0]],[[0,0],[0,0]],[[-22310,-198],[-198,0]],[[0,0],[0,0]],[[-9397,-426],[-426,0]],[[0,0],[0,0]],[[-1761,-368],[-368,0]],[[0,0],[0,0]],[[-63,-105],[-105,-2]],[[0],[0,0]],[[0],[0,-7]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
