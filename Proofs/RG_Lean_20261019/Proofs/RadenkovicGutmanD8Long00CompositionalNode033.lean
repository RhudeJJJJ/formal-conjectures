/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode030
import Proofs.RadenkovicGutmanD8Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,8]],[[0,0],[0]],[[-72,72],[72]],[[0,0],[0]],[[24,192],[192]],[[0,0],[0]],[[1336,176],[176]],[[0,0],[0]],[[4112,64],[64]],[[0,0],[0]],[[6048,8],[8]],[[0]],[[5088]],[[0]],[[2552]],[[0]],[[752]],[[0]],[[120]],[[0]],[[8]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
