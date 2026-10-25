/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode065
import Proofs.RadenkovicGutmanD21Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-97,0],[0,0]],[[0,0],[0,0]],[[-1273,0],[0,0]],[[0,0],[0,0]],[[-8018,0],[0,0]],[[0,0],[0,0]],[[-28669,0],[0,0]],[[0,0],[0,0]],[[-61920,-2],[-2,0]],[[0,0],[0,0]],[[-81736,-79],[-79,0]],[[0,0],[0,0]],[[-64142,-506],[-506,0]],[[0,0],[0,0]],[[-27555,-1182],[-1182,0]],[[0,0],[0,0]],[[-5247,-1068],[-1068,0]],[[0,0],[0,0]],[[-189,-315],[-315,-2]],[[0],[0,0]],[[0],[0,-21]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
