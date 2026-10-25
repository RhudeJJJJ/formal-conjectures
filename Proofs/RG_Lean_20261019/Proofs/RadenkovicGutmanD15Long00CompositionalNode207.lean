/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode065
import Proofs.RadenkovicGutmanD15Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-79,0],[0,0]],[[0,0],[0,0]],[[-979,0],[0,0]],[[0,0],[0,0]],[[-6002,0],[0,0]],[[0,0],[0,0]],[[-21127,0],[0,0]],[[0,0],[0,0]],[[-45168,-2],[-2,0]],[[0,0],[0,0]],[[-59200,-61],[-61,0]],[[0,0],[0,0]],[[-46214,-374],[-374,0]],[[0,0],[0,0]],[[-19773,-858],[-858,0]],[[0,0],[0,0]],[[-3753,-768],[-768,0]],[[0,0],[0,0]],[[-135,-225],[-225,-2]],[[0],[0,0]],[[0],[0,-15]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
