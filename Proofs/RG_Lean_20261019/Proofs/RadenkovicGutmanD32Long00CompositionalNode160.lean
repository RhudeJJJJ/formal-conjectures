/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode159
import Proofs.RadenkovicGutmanD32Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-450,0],[0,0]],[[0,0],[0,0]],[[-2820,0],[0,0]],[[0,0],[0,0]],[[-9570,0],[0,0]],[[0,0],[0,0]],[[-19080,0],[0,0]],[[0,0],[0,0]],[[-22680,-30],[-30,0]],[[0,0],[0,0]],[[-15420,-240],[-240,0]],[[0,0],[0,0]],[[-5010,-660],[-660,0]],[[0,0],[0,0]],[[-90,-720],[-720,0]],[[0,0],[0,0]],[[270,-270],[-270,0]],[[0],[0,0]],[[0],[0,-30]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
