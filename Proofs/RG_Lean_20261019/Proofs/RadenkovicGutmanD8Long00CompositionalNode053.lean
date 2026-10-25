/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode030
import Proofs.RadenkovicGutmanD8Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,8]],[[0,0],[0]],[[72,72],[72]],[[0,0],[0]],[[1272,192],[192]],[[0,0],[0]],[[5576,176],[176]],[[0,0],[0]],[[11440,64],[64]],[[0,0],[0]],[[13152,8],[8]],[[0]],[[9088]],[[0]],[[3848]],[[0]],[[976]],[[0]],[[136]],[[0]],[[8]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
