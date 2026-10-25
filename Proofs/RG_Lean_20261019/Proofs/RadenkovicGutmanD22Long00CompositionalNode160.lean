/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode159
import Proofs.RadenkovicGutmanD22Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-300,0],[0,0]],[[0,0],[0,0]],[[-1880,0],[0,0]],[[0,0],[0,0]],[[-6380,0],[0,0]],[[0,0],[0,0]],[[-12720,0],[0,0]],[[0,0],[0,0]],[[-15120,-20],[-20,0]],[[0,0],[0,0]],[[-10280,-160],[-160,0]],[[0,0],[0,0]],[[-3340,-440],[-440,0]],[[0,0],[0,0]],[[-60,-480],[-480,0]],[[0,0],[0,0]],[[180,-180],[-180,0]],[[0],[0,0]],[[0],[0,-20]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
