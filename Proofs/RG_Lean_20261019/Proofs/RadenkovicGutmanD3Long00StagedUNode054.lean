/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e054 : NestedArithmetic.Expr 3 := .scaled (-1) e053
noncomputable def p054 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[-9]],[[0]],[[-78]],[[0]],[[-265]],[[0]],[[-458]],[[0]],[[-444]],[[0]],[[-250]],[[0]],[[-81]],[[0]],[[-14]],[[0]],[[-1]]]
theorem step054 : p054=NestedHorner.scale (-1) p053 := by decide +kernel
#print axioms step054
theorem h054 : NestedArithmetic.compile e054=p054 := StagedExprCompile.compile_scaled (-1) e054 e053 p053 p054 rfl h053 step054
#print axioms h054
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
