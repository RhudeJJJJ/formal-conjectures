/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode065
import Proofs.RadenkovicGutmanD21Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-21]],[[0,0],[0,0]],[[-189,-315],[-315,-2]],[[0,0],[0]],[[-5247,-1068],[-1068]],[[0,0],[0]],[[-27555,-1182],[-1182]],[[0,0],[0]],[[-64142,-506],[-506]],[[0,0],[0]],[[-81736,-79],[-79]],[[0,0],[0]],[[-61920,-2],[-2]],[[0]],[[-28669]],[[0]],[[-8018]],[[0]],[[-1273]],[[0]],[[-97]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
