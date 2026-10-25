/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode037
import Proofs.RadenkovicGutmanD10Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-8]],[[0,0],[0]],[[72,-72],[-72]],[[0,0],[0]],[[-24,-192],[-192]],[[0,0],[0]],[[-1336,-176],[-176]],[[0,0],[0]],[[-4112,-64],[-64]],[[0,0],[0]],[[-6048,-8],[-8]],[[0]],[[-5088]],[[0]],[[-2552]],[[0]],[[-752]],[[0]],[[-120]],[[0]],[[-8]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
