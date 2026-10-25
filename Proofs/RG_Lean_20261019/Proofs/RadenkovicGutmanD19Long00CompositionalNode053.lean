/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode030
import Proofs.RadenkovicGutmanD19Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,19]],[[0,0],[0]],[[171,171],[171]],[[0,0],[0]],[[3021,456],[456]],[[0,0],[0]],[[13243,418],[418]],[[0,0],[0]],[[27170,152],[152]],[[0,0],[0]],[[31236,19],[19]],[[0]],[[21584]],[[0]],[[9139]],[[0]],[[2318]],[[0]],[[323]],[[0]],[[19]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
