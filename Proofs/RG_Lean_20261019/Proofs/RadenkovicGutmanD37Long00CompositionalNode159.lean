/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode037
import Proofs.RadenkovicGutmanD37Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-35],[0]],[[0,0],[0]],[[-525,0],[0,0]],[[0,0],[0,0]],[[-3290,0],[0,0]],[[0,0],[0,0]],[[-11165,0],[0,0]],[[0,0],[0,0]],[[-22260,0],[0,0]],[[0,0],[0,0]],[[-26460,-35],[-35,0]],[[0,0],[0,0]],[[-17990,-280],[-280,0]],[[0,0],[0,0]],[[-5845,-770],[-770,0]],[[0,0],[0,0]],[[-105,-840],[-840,0]],[[0,0],[0,0]],[[315,-315],[-315,0]],[[0],[0,0]],[[0],[0,-35]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
