/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .scaled (-1) e052
noncomputable def p053 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[-9]],[[0]],[[-78]],[[0]],[[-265]],[[0]],[[-458]],[[0]],[[-444]],[[0]],[[-250]],[[0]],[[-81]],[[0]],[[-14]],[[0]],[[-1]]]
theorem step053 : p053=NestedHorner.scale (-1) p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_scaled (-1) e053 e052 p052 p053 rfl h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
