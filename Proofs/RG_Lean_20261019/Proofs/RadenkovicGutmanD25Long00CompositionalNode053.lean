/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode030
import Proofs.RadenkovicGutmanD25Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,25]],[[0,0],[0]],[[225,225],[225]],[[0,0],[0]],[[3975,600],[600]],[[0,0],[0]],[[17425,550],[550]],[[0,0],[0]],[[35750,200],[200]],[[0,0],[0]],[[41100,25],[25]],[[0]],[[28400]],[[0]],[[12025]],[[0]],[[3050]],[[0]],[[425]],[[0]],[[25]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
