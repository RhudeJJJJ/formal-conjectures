/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode065
import Proofs.RadenkovicGutmanD35Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-139,0],[0,0]],[[0,0],[0,0]],[[-1959,0],[0,0]],[[0,0],[0,0]],[[-12722,0],[0,0]],[[0,0],[0,0]],[[-46267,0],[0,0]],[[0,0],[0,0]],[[-101008,-2],[-2,0]],[[0,0],[0,0]],[[-134320,-121],[-121,0]],[[0,0],[0,0]],[[-105974,-814],[-814,0]],[[0,0],[0,0]],[[-45713,-1938],[-1938,0]],[[0,0],[0,0]],[[-8733,-1768],[-1768,0]],[[0,0],[0,0]],[[-315,-525],[-525,-2]],[[0],[0,0]],[[0],[0,-35]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
