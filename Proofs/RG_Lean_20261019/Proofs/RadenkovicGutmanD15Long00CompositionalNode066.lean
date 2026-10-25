/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode065
import Proofs.RadenkovicGutmanD15Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-15]],[[0,0],[0,0]],[[-135,-225],[-225,-2]],[[0,0],[0]],[[-3753,-768],[-768]],[[0,0],[0]],[[-19773,-858],[-858]],[[0,0],[0]],[[-46214,-374],[-374]],[[0,0],[0]],[[-59200,-61],[-61]],[[0,0],[0]],[[-45168,-2],[-2]],[[0]],[[-21127]],[[0]],[[-6002]],[[0]],[[-979]],[[0]],[[-79]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
