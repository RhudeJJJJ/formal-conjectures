/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode037
import Proofs.RadenkovicGutmanD41Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-39]],[[0,0],[0]],[[351,-351],[-351]],[[0,0],[0]],[[-117,-936],[-936]],[[0,0],[0]],[[-6513,-858],[-858]],[[0,0],[0]],[[-20046,-312],[-312]],[[0,0],[0]],[[-29484,-39],[-39]],[[0]],[[-24804]],[[0]],[[-12441]],[[0]],[[-3666]],[[0]],[[-585]],[[0]],[[-39]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
