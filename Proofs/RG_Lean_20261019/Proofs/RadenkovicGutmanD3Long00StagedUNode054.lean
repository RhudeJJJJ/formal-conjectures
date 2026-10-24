/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode053
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e054 : NestedArithmetic.Expr 3 := .scaled (-1) e053
noncomputable def p054 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[-9]],[[0]],[[-78]],[[0]],[[-265]],[[0]],[[-458]],[[0]],[[-444]],[[0]],[[-250]],[[0]],[[-81]],[[0]],[[-14]],[[0]],[[-1]]]
theorem step054 : p054=NestedHorner.scale (-1) p053 := by decide +kernel
#print axioms step054
theorem h054 : NestedArithmetic.compile e054=p054 := by
  change NestedHorner.scale (-1) (NestedArithmetic.compile e053)=p054
  rw [h053]
  exact step054.symm
#print axioms h054
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
