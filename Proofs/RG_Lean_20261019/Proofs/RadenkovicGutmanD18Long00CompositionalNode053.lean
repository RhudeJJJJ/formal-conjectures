/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode030
import Proofs.RadenkovicGutmanD18Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,18]],[[0,0],[0]],[[162,162],[162]],[[0,0],[0]],[[2862,432],[432]],[[0,0],[0]],[[12546,396],[396]],[[0,0],[0]],[[25740,144],[144]],[[0,0],[0]],[[29592,18],[18]],[[0]],[[20448]],[[0]],[[8658]],[[0]],[[2196]],[[0]],[[306]],[[0]],[[18]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
