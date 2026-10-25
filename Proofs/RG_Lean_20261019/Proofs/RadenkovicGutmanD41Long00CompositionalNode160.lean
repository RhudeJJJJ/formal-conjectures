/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode159
import Proofs.RadenkovicGutmanD41Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-39],[0]],[[0,0],[0]],[[-585,0],[0,0]],[[0,0],[0,0]],[[-3666,0],[0,0]],[[0,0],[0,0]],[[-12441,0],[0,0]],[[0,0],[0,0]],[[-24804,0],[0,0]],[[0,0],[0,0]],[[-29484,-39],[-39,0]],[[0,0],[0,0]],[[-20046,-312],[-312,0]],[[0,0],[0,0]],[[-6513,-858],[-858,0]],[[0,0],[0,0]],[[-117,-936],[-936,0]],[[0,0],[0,0]],[[351,-351],[-351,0]],[[0],[0,0]],[[0],[0,-39]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
