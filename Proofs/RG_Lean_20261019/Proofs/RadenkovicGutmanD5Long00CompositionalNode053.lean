/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode030
import Proofs.RadenkovicGutmanD5Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,5]],[[0,0],[0]],[[45,45],[45]],[[0,0],[0]],[[795,120],[120]],[[0,0],[0]],[[3485,110],[110]],[[0,0],[0]],[[7150,40],[40]],[[0,0],[0]],[[8220,5],[5]],[[0]],[[5680]],[[0]],[[2405]],[[0]],[[610]],[[0]],[[85]],[[0]],[[5]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
