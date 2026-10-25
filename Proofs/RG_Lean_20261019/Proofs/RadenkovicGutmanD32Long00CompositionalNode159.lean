/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode037
import Proofs.RadenkovicGutmanD32Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-450,0],[0,0]],[[0,0],[0,0]],[[-2820,0],[0,0]],[[0,0],[0,0]],[[-9570,0],[0,0]],[[0,0],[0,0]],[[-19080,0],[0,0]],[[0,0],[0,0]],[[-22680,-30],[-30,0]],[[0,0],[0,0]],[[-15420,-240],[-240,0]],[[0,0],[0,0]],[[-5010,-660],[-660,0]],[[0,0],[0,0]],[[-90,-720],[-720,0]],[[0,0],[0,0]],[[270,-270],[-270,0]],[[0],[0,0]],[[0],[0,-30]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
