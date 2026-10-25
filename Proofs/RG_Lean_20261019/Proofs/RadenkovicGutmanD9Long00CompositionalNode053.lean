/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode030
import Proofs.RadenkovicGutmanD9Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,9]],[[0,0],[0]],[[81,81],[81]],[[0,0],[0]],[[1431,216],[216]],[[0,0],[0]],[[6273,198],[198]],[[0,0],[0]],[[12870,72],[72]],[[0,0],[0]],[[14796,9],[9]],[[0]],[[10224]],[[0]],[[4329]],[[0]],[[1098]],[[0]],[[153]],[[0]],[[9]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
