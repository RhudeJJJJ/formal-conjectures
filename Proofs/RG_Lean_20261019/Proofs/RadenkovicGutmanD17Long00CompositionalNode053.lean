/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode030
import Proofs.RadenkovicGutmanD17Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,17]],[[0,0],[0]],[[153,153],[153]],[[0,0],[0]],[[2703,408],[408]],[[0,0],[0]],[[11849,374],[374]],[[0,0],[0]],[[24310,136],[136]],[[0,0],[0]],[[27948,17],[17]],[[0]],[[19312]],[[0]],[[8177]],[[0]],[[2074]],[[0]],[[289]],[[0]],[[17]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
