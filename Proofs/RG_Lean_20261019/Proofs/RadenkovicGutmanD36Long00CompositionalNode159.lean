/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode037
import Proofs.RadenkovicGutmanD36Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-510,0],[0,0]],[[0,0],[0,0]],[[-3196,0],[0,0]],[[0,0],[0,0]],[[-10846,0],[0,0]],[[0,0],[0,0]],[[-21624,0],[0,0]],[[0,0],[0,0]],[[-25704,-34],[-34,0]],[[0,0],[0,0]],[[-17476,-272],[-272,0]],[[0,0],[0,0]],[[-5678,-748],[-748,0]],[[0,0],[0,0]],[[-102,-816],[-816,0]],[[0,0],[0,0]],[[306,-306],[-306,0]],[[0],[0,0]],[[0],[0,-34]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
