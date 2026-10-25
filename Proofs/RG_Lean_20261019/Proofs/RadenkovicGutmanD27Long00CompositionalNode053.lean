/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode030
import Proofs.RadenkovicGutmanD27Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,27]],[[0,0],[0]],[[243,243],[243]],[[0,0],[0]],[[4293,648],[648]],[[0,0],[0]],[[18819,594],[594]],[[0,0],[0]],[[38610,216],[216]],[[0,0],[0]],[[44388,27],[27]],[[0]],[[30672]],[[0]],[[12987]],[[0]],[[3294]],[[0]],[[459]],[[0]],[[27]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
