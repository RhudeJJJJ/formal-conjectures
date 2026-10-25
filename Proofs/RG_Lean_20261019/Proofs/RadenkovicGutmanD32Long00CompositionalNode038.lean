/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode037
import Proofs.RadenkovicGutmanD32Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-30]],[[0,0],[0]],[[270,-270],[-270]],[[0,0],[0]],[[-90,-720],[-720]],[[0,0],[0]],[[-5010,-660],[-660]],[[0,0],[0]],[[-15420,-240],[-240]],[[0,0],[0]],[[-22680,-30],[-30]],[[0]],[[-19080]],[[0]],[[-9570]],[[0]],[[-2820]],[[0]],[[-450]],[[0]],[[-30]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
