/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode000
import Proofs.RadenkovicGutmanD3Long00StagedUNode014
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e000 e014
noncomputable def p053 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[9]],[[0]],[[78]],[[0]],[[265]],[[0]],[[458]],[[0]],[[444]],[[0]],[[250]],[[0]],[[81]],[[0]],[[14]],[[0]],[[1]]]
theorem step053 : p053=NestedArithmetic.mul p000 p014 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e000) (NestedArithmetic.compile e014)=p053
  rw [h000,h014]
  exact step053.symm
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
