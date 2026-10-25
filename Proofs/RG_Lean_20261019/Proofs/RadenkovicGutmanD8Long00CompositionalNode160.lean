/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode159
import Proofs.RadenkovicGutmanD8Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-90,0],[0,0]],[[0,0],[0,0]],[[-564,0],[0,0]],[[0,0],[0,0]],[[-1914,0],[0,0]],[[0,0],[0,0]],[[-3816,0],[0,0]],[[0,0],[0,0]],[[-4536,-6],[-6,0]],[[0,0],[0,0]],[[-3084,-48],[-48,0]],[[0,0],[0,0]],[[-1002,-132],[-132,0]],[[0,0],[0,0]],[[-18,-144],[-144,0]],[[0,0],[0,0]],[[54,-54],[-54,0]],[[0],[0,0]],[[0],[0,-6]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
