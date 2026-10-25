/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode037
import Proofs.RadenkovicGutmanD8Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-6]],[[0,0],[0]],[[54,-54],[-54]],[[0,0],[0]],[[-18,-144],[-144]],[[0,0],[0]],[[-1002,-132],[-132]],[[0,0],[0]],[[-3084,-48],[-48]],[[0,0],[0]],[[-4536,-6],[-6]],[[0]],[[-3816]],[[0]],[[-1914]],[[0]],[[-564]],[[0]],[[-90]],[[0]],[[-6]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
