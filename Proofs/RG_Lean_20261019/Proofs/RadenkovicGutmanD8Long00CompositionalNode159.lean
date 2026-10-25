/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode037
import Proofs.RadenkovicGutmanD8Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-90,0],[0,0]],[[0,0],[0,0]],[[-564,0],[0,0]],[[0,0],[0,0]],[[-1914,0],[0,0]],[[0,0],[0,0]],[[-3816,0],[0,0]],[[0,0],[0,0]],[[-4536,-6],[-6,0]],[[0,0],[0,0]],[[-3084,-48],[-48,0]],[[0,0],[0,0]],[[-1002,-132],[-132,0]],[[0,0],[0,0]],[[-18,-144],[-144,0]],[[0,0],[0,0]],[[54,-54],[-54,0]],[[0],[0,0]],[[0],[0,-6]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
