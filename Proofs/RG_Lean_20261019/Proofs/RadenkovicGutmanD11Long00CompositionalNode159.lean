/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode037
import Proofs.RadenkovicGutmanD11Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-9],[0]],[[0,0],[0]],[[-135,0],[0,0]],[[0,0],[0,0]],[[-846,0],[0,0]],[[0,0],[0,0]],[[-2871,0],[0,0]],[[0,0],[0,0]],[[-5724,0],[0,0]],[[0,0],[0,0]],[[-6804,-9],[-9,0]],[[0,0],[0,0]],[[-4626,-72],[-72,0]],[[0,0],[0,0]],[[-1503,-198],[-198,0]],[[0,0],[0,0]],[[-27,-216],[-216,0]],[[0,0],[0,0]],[[81,-81],[-81,0]],[[0],[0,0]],[[0],[0,-9]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
