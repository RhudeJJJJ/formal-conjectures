/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode016
import Proofs.RadenkovicGutmanD3Long00StagedUNode020
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e021 : NestedArithmetic.Expr 3 := .plus e016 e020
noncomputable def p021 : NestedHorner.Poly 3 := [[[]],[[0]],[[9]],[[0]],[[24]],[[0]],[[22]],[[0]],[[8]],[[0]],[[1]]]
theorem step021 : p021=NestedHorner.add p016 p020 := by decide +kernel
#print axioms step021
theorem h021 : NestedArithmetic.compile e021=p021 := by
  change NestedHorner.add (NestedArithmetic.compile e016) (NestedArithmetic.compile e020)=p021
  rw [h016,h020]
  exact step021.symm
#print axioms h021
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
