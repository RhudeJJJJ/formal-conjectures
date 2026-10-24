/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode037
import Proofs.RadenkovicGutmanD5Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-3],[0]],[[0,0],[0]],[[-45,0],[0,0]],[[0,0],[0,0]],[[-282,0],[0,0]],[[0,0],[0,0]],[[-957,0],[0,0]],[[0,0],[0,0]],[[-1908,0],[0,0]],[[0,0],[0,0]],[[-2268,-3],[-3,0]],[[0,0],[0,0]],[[-1542,-24],[-24,0]],[[0,0],[0,0]],[[-501,-66],[-66,0]],[[0,0],[0,0]],[[-9,-72],[-72,0]],[[0,0],[0,0]],[[27,-27],[-27,0]],[[0],[0,0]],[[0],[0,-3]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
