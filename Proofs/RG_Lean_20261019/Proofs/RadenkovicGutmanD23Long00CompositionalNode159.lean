/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode037
import Proofs.RadenkovicGutmanD23Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-21],[0]],[[0,0],[0]],[[-315,0],[0,0]],[[0,0],[0,0]],[[-1974,0],[0,0]],[[0,0],[0,0]],[[-6699,0],[0,0]],[[0,0],[0,0]],[[-13356,0],[0,0]],[[0,0],[0,0]],[[-15876,-21],[-21,0]],[[0,0],[0,0]],[[-10794,-168],[-168,0]],[[0,0],[0,0]],[[-3507,-462],[-462,0]],[[0,0],[0,0]],[[-63,-504],[-504,0]],[[0,0],[0,0]],[[189,-189],[-189,0]],[[0],[0,0]],[[0],[0,-21]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
