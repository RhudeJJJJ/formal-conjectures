/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode030
import Proofs.RadenkovicGutmanD13Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,13]],[[0,0],[0]],[[117,117],[117]],[[0,0],[0]],[[2067,312],[312]],[[0,0],[0]],[[9061,286],[286]],[[0,0],[0]],[[18590,104],[104]],[[0,0],[0]],[[21372,13],[13]],[[0]],[[14768]],[[0]],[[6253]],[[0]],[[1586]],[[0]],[[221]],[[0]],[[13]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
