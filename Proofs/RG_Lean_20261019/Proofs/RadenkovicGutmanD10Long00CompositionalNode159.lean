/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode037
import Proofs.RadenkovicGutmanD10Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-120,0],[0,0]],[[0,0],[0,0]],[[-752,0],[0,0]],[[0,0],[0,0]],[[-2552,0],[0,0]],[[0,0],[0,0]],[[-5088,0],[0,0]],[[0,0],[0,0]],[[-6048,-8],[-8,0]],[[0,0],[0,0]],[[-4112,-64],[-64,0]],[[0,0],[0,0]],[[-1336,-176],[-176,0]],[[0,0],[0,0]],[[-24,-192],[-192,0]],[[0,0],[0,0]],[[72,-72],[-72,0]],[[0],[0,0]],[[0],[0,-8]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
