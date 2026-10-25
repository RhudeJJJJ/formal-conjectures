/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode037
import Proofs.RadenkovicGutmanD22Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-300,0],[0,0]],[[0,0],[0,0]],[[-1880,0],[0,0]],[[0,0],[0,0]],[[-6380,0],[0,0]],[[0,0],[0,0]],[[-12720,0],[0,0]],[[0,0],[0,0]],[[-15120,-20],[-20,0]],[[0,0],[0,0]],[[-10280,-160],[-160,0]],[[0,0],[0,0]],[[-3340,-440],[-440,0]],[[0,0],[0,0]],[[-60,-480],[-480,0]],[[0,0],[0,0]],[[180,-180],[-180,0]],[[0],[0,0]],[[0],[0,-20]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
