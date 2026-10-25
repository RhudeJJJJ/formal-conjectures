/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode159
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-9],[0]],[[0,0],[0]],[[-135,0],[0,0]],[[0,0],[0,0]],[[-846,0],[0,0]],[[0,0],[0,0]],[[-2871,0],[0,0]],[[0,0],[0,0]],[[-5724,0],[0,0]],[[0,0],[0,0]],[[-6804,-9],[-9,0]],[[0,0],[0,0]],[[-4626,-72],[-72,0]],[[0,0],[0,0]],[[-1503,-198],[-198,0]],[[0,0],[0,0]],[[-27,-216],[-216,0]],[[0,0],[0,0]],[[81,-81],[-81,0]],[[0],[0,0]],[[0],[0,-9]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
