/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode037
import Proofs.RadenkovicGutmanD41Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-39],[0]],[[0,0],[0]],[[-585,0],[0,0]],[[0,0],[0,0]],[[-3666,0],[0,0]],[[0,0],[0,0]],[[-12441,0],[0,0]],[[0,0],[0,0]],[[-24804,0],[0,0]],[[0,0],[0,0]],[[-29484,-39],[-39,0]],[[0,0],[0,0]],[[-20046,-312],[-312,0]],[[0,0],[0,0]],[[-6513,-858],[-858,0]],[[0,0],[0,0]],[[-117,-936],[-936,0]],[[0,0],[0,0]],[[351,-351],[-351,0]],[[0],[0,0]],[[0],[0,-39]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
